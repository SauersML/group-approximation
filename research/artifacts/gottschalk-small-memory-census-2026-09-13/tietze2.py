#!/usr/bin/env python3
"""Exact word problem after Tietze elimination, in three solvable cases.

After greedy Tietze elimination (tietze.py) the presentation has generators R and relators Q.
  * |R| <= 1: cyclic of order gcd of exponent sums (tietze.py).
  * Q empty: free on R. Two words are equal iff their substituted, freely reduced forms agree.
  * |R| = 2 and every relator in Q is a cyclic conjugate of [g,h]^(+-1): free abelian of rank 2.
    Two words are equal iff their exponent vectors agree.
Anything else is reported as undecided, never guessed.

Usage: tietze2.py tables.jsonl out.jsonl [oracle.jsonl]
With an oracle file, decided tables that the oracle resolved are cross-checked.
"""
import json, math, sys
import tietze as T

def rotations(w):
    return [tuple(w[i:] + w[:i]) for i in range(len(w))]

def is_commutator_relator(r, g, h):
    targets = set()
    for a, b in ((g, h), (h, g)):
        c = [a, b, T.inv(a), T.inv(b)]
        targets |= set(rotations(c))
    return tuple(r) in targets

def decide(t):
    rem, rels, sub, order = T.tietze(t["gens"], t["rels"])
    if len(rem) <= 1:
        d = T.decide(t)
        d["kind"] = "cyclic"
        return d
    def full(w):
        return tuple(T.subst(list(w), sub))
    if not rels:
        kind, key = "free", full
    elif len(rem) == 2 and all(is_commutator_relator(r, rem[0], rem[1]) for r in rels):
        kind = "free-abelian-2"
        def key(w):
            v = full(w)
            return tuple(sum((-1 if y.endswith("'") else 1) for y in v if T.base(y) == g) for g in rem)
    else:
        return {"id": t["id"], "kind": "undecided", "remaining": rem, "relators": rels}
    def classes(dd):
        groups = {}
        for c, w in dd.items():
            groups.setdefault(key(w), []).append(c)
        return sorted(sorted(b) for b in groups.values())
    ns, nm = t["ns"], t["nm"]
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    lab = t["labels"]
    distinct = len({key(lab[a]) for a in S}) == ns and len({key(lab[a]) for a in M}) == nm
    return {"id": t["id"], "kind": kind, "remaining": rem, "eliminated": order,
            "fwd_classes": classes(t["fwd"]), "rev_classes": classes(t["rev"]),
            "labels_distinct": distinct, "resolved": True, "nreps": 0, "undecided": [],
            "certificate": "tietze-" + kind}

def norm(blocks):
    return {frozenset(b) for b in blocks}

def main(inp, out, oracle_path=None):
    orc = {r["id"]: r for r in map(json.loads, open(oracle_path))} if oracle_path else {}
    counts, checked, mismatch, bad = {}, 0, 0, []
    with open(out, "w") as fh:
        for line in open(inp):
            t = json.loads(line)
            d = decide(t)
            fh.write(json.dumps(d) + "\n")
            counts[d["kind"]] = counts.get(d["kind"], 0) + 1
            if d["kind"] == "undecided":
                continue
            o = orc.get(t["id"])
            if o and o["resolved"]:
                checked += 1
                if (norm(o["fwd_classes"]) != norm(d["fwd_classes"]) or
                        norm(o["rev_classes"]) != norm(d["rev_classes"]) or
                        o["labels_distinct"] != d["labels_distinct"]):
                    mismatch += 1
                    bad.append(t["id"])
    print(json.dumps({"input": inp, "kinds": counts, "cross_checked": checked,
                      "mismatch": mismatch, "mismatch_ids": bad[:20]}))

if __name__ == "__main__":
    sys.path.insert(0, ".")
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None)
