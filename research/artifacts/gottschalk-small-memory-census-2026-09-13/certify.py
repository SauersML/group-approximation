#!/usr/bin/env python3
"""Independent certificate pass for the realized tables claimed by oracle.py.

For every table and every pair of words in the forward, reverse and label lists:
  * if oracle.py put them in one class: find an explicit rewriting derivation
    (relators applied at positions, plus free reduction) and replay it step by step;
  * if oracle.py put them in different classes: find permutation images of the
    generators that satisfy every relator exactly and separate the two words, and
    re-evaluate both.
Output per table: {"id", "ok": bool, "equal_certs": [...], "distinct_certs": [...]},
where a distinct certificate stores the separating images, so a reader can re-check it
by hand, and an equal certificate stores the derivation as a list of words.
"""
import json, os, random, sys
from collections import deque
sys.path.insert(0, ".")
import oracle as O

MAXLENS = [int(x) for x in os.environ.get("CERT_MAXLENS", "10").split(",")]
MAXNODES = int(os.environ.get("CERT_MAXNODES", "400000"))

def derivation(w1, w2, rules, maxlen=8, maxnodes=400000):
    start, goal = O.reduce_word(w1), O.reduce_word(w2)
    if start == goal:
        return [list(start)]
    prev = {start: None}
    dq = deque([start])
    pieces = []
    for a, b in rules:
        p = O.reduce_word(a + tuple(O.inv(g) for g in reversed(b)))
        if p:
            pieces.append(p)
    while dq and len(prev) < maxnodes:
        w = dq.popleft()
        succ = []
        for a, b in rules:
            la = len(a)
            for i in range(len(w) - la + 1):
                if w[i:i + la] == a:
                    succ.append(O.reduce_word(w[:i] + b + w[i + la:]))
        for p in pieces:
            for i in range(len(w) + 1):
                succ.append(O.reduce_word(w[:i] + p + w[i:]))
        for nw in succ:
            if len(nw) > maxlen or nw in prev:
                continue
            prev[nw] = w
            if nw == goal:
                path, cur = [], nw
                while cur is not None:
                    path.append(list(cur))
                    cur = prev[cur]
                return path[::-1]
            dq.append(nw)
    return None

def replay(path, rules):
    # each consecutive pair must differ by one relator application or relator insertion
    rels = set()
    for a, b in rules:
        rels.add((a, b))
    for u, v in zip(path, path[1:]):
        u, v = tuple(u), tuple(v)
        ok = False
        for a, b in rules:
            la = len(a)
            for i in range(len(u) - la + 1):
                if u[i:i + la] == a and O.reduce_word(u[:i] + b + u[i + la:]) == v:
                    ok = True
                    break
            if ok:
                break
            p = O.reduce_word(a + tuple(O.inv(g) for g in reversed(b)))
            for i in range(len(u) + 1):
                if p and O.reduce_word(u[:i] + p + u[i:]) == v:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            return False
    return True

def main(tables_path, oracle_path, out, seed=7):
    rng = random.Random(seed)
    oracle = {r["id"]: r for r in map(json.loads, open(oracle_path))}
    n_ok = n_bad = 0
    with open(out, "w") as fh:
        for line in open(tables_path):
            t = json.loads(line)
            o = oracle.get(t["id"])
            if o is None or not o["resolved"]:
                continue
            gens, rels = t["gens"], t["rels"]
            rules = O.relator_rules(rels)
            words = {"F:" + k: w for k, w in t["fwd"].items()}
            words.update({"R:" + k: w for k, w in t["rev"].items()})
            words.update({"L:" + k: w for k, w in t["labels"].items()})
            cls = {}
            for pre, blocks in (("F:", o["fwd_classes"]), ("R:", o["rev_classes"])):
                for i, b in enumerate(blocks):
                    for c in b:
                        cls[pre + c] = pre + str(i)
            keys = [k for k in words if k[:2] in ("F:", "R:")]
            reps = []
            for n in range(2, 7):
                reps += [(n, r) for r in O.find_reps(gens, rels, n, 3000, rng)]
            ok = True
            eq_certs, ds_certs = [], []
            for i, a in enumerate(keys):
                for b in keys[i + 1:]:
                    if a[:2] != b[:2]:
                        continue
                    if cls[a] == cls[b]:
                        # the move set (relator insertion, free reduction) is not
                        # symmetric, so search from either end; a path in either
                        # direction certifies equality
                        path = None
                        for ml in MAXLENS:
                            path = derivation(words[a], words[b], rules, maxlen=ml, maxnodes=MAXNODES)
                            if path is None:
                                path = derivation(words[b], words[a], rules, maxlen=ml, maxnodes=MAXNODES)
                            if path is not None:
                                break
                        if path is None or not replay(path, rules):
                            ok = False
                        else:
                            eq_certs.append({"pair": [a, b], "path": path})
                    else:
                        found = None
                        for n, r in reps:
                            if all(O.evaluate(u, r, n) == O.evaluate(v, r, n) for u, v in rels) and \
                               O.evaluate(words[a], r, n) != O.evaluate(words[b], r, n):
                                found = {"pair": [a, b], "n": n,
                                         "images": {g: list(p) for g, p in r.items()}}
                                break
                        if found is None:
                            ok = False
                        else:
                            ds_certs.append(found)
            n_ok += ok
            n_bad += (not ok)
            fh.write(json.dumps({"id": t["id"], "ok": ok, "equal_certs": eq_certs,
                                 "distinct_certs": ds_certs}) + "\n")
    print(json.dumps({"tables": tables_path, "certified": n_ok, "failed": n_bad}))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 7)
