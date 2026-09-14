#!/usr/bin/env python3
"""Exact word problem by Tietze elimination, for presentations that collapse to a cyclic group.

A relator in which some generator g occurs exactly once, r = u g^(+-1) v with u, v free of g,
is a Tietze move: g = (u^-1 v^-1)^(+-1) and r is dropped. Eliminate greedily. If at most one
generator g0 remains, the group is cyclic of order n = gcd(|exponent sums of the remaining
relators|) (n = 0 means infinite cyclic), and two words are equal iff their g0-exponent sums
after full substitution agree mod n. This decides every pair exactly, with no search.

Usage: tietze.py tables.jsonl out.jsonl [oracle.jsonl]
With an oracle file, every table that is cyclic AND resolved by the oracle is cross-checked
(partitions must agree); the summary reports mismatches.
"""
import json, math, sys

def inv(g):
    return g[:-1] if g.endswith("'") else g + "'"

def base(g):
    return g.rstrip("'")

def red(w):
    out = []
    for g in w:
        if out and out[-1] == inv(g):
            out.pop()
        else:
            out.append(g)
    return out

def winv(w):
    return [inv(g) for g in reversed(w)]

def subst(w, sub):
    out = []
    for g in w:
        b = base(g)
        if b in sub:
            out += sub[b] if not g.endswith("'") else winv(sub[b])
        else:
            out.append(g)
    return red(out)

def tietze(gens, rels):
    rels = [red(list(u) + winv(list(v))) for u, v in rels]
    rels = [r for r in rels if r]
    sub, order, remaining = {}, [], list(gens)
    changed = True
    while changed:
        changed = False
        for i, r in enumerate(rels):
            counts = {}
            for g in r:
                counts[base(g)] = counts.get(base(g), 0) + 1
            cand = [g for g in remaining if counts.get(g, 0) == 1]
            if not cand:
                continue
            g = cand[0]
            k = next(j for j, x in enumerate(r) if base(x) == g)
            u, x, v = r[:k], r[k], r[k + 1:]
            expr = red(winv(u) + winv(v))          # u x v = 1  =>  x = u^-1 v^-1
            if x.endswith("'"):
                expr = winv(expr)
            assert all(base(y) != g for y in expr)
            rels = [subst(rr, {g: expr}) for j, rr in enumerate(rels) if j != i]
            rels = [rr for rr in rels if rr]
            for h in list(sub):
                sub[h] = subst(sub[h], {g: expr})
            sub[g] = expr
            order.append(g)
            remaining.remove(g)
            changed = True
            break
    return remaining, rels, sub, order

def decide(t):
    rem, rels, sub, order = tietze(t["gens"], t["rels"])
    if len(rem) > 1:
        return {"id": t["id"], "cyclic": False, "remaining": rem}
    g0 = rem[0] if rem else None
    def expo(w):
        w = subst(list(w), sub)
        assert all(base(y) == g0 for y in w)
        return sum(-1 if y.endswith("'") else 1 for y in w)
    n = 0
    for r in rels:
        n = math.gcd(n, abs(expo(r)))
    def key(w):
        e = expo(w)
        return e % n if n else e
    def classes(d):
        groups = {}
        for c, w in d.items():
            groups.setdefault(key(w), []).append(c)
        return sorted(sorted(b) for b in groups.values())
    ns, nm = t["ns"], t["nm"]
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    lab = t["labels"]
    distinct = len({key(lab[a]) for a in S}) == ns and len({key(lab[a]) for a in M}) == nm
    return {"id": t["id"], "cyclic": True, "order": n, "generator": g0, "eliminated": order,
            "fwd_classes": classes(t["fwd"]), "rev_classes": classes(t["rev"]),
            "labels_distinct": distinct, "resolved": True, "nreps": 0, "undecided": [],
            "certificate": "tietze-cyclic"}

def norm(blocks):
    return {frozenset(b) for b in blocks}

def main(inp, out, oracle_path=None):
    orc = {r["id"]: r for r in map(json.loads, open(oracle_path))} if oracle_path else {}
    n = cyc = checked = mismatch = 0
    bad = []
    with open(out, "w") as fh:
        for line in open(inp):
            t = json.loads(line)
            n += 1
            d = decide(t)
            fh.write(json.dumps(d) + "\n")
            if not d["cyclic"]:
                continue
            cyc += 1
            o = orc.get(t["id"])
            if o and o["resolved"]:
                checked += 1
                if (norm(o["fwd_classes"]) != norm(d["fwd_classes"]) or
                        norm(o["rev_classes"]) != norm(d["rev_classes"]) or
                        o["labels_distinct"] != d["labels_distinct"]):
                    mismatch += 1
                    bad.append(t["id"])
    print(json.dumps({"input": inp, "tables": n, "cyclic": cyc, "cross_checked": checked,
                      "mismatch": mismatch, "mismatch_ids": bad[:20]}))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None)
