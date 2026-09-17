"""Reduce the vector v = (p, -q) of a Cohn matrix C(p,q) under E_2(R), R = Z[t,t^-1].

Since C(Yv) = Y C(v) Y^{-1} for Y in SL_2(R) (proof node
sl2-laurent-elementary-iff-three-unipotent-conditions-proof, Lemma 3), C(p,q) is
elementary whenever v is E_2-equivalent to a vector with a unit coordinate: then
the vector is E_2-equivalent to (0, u) or (u, 0) and C is E_2-conjugate to
E_21(-u^2) or E_12(u^2).  This is a two-entry search, far cheaper than the matrix
search.  Output 'unit' = certified elementary (a path exists); 'const n' = reached
a vector with a constant coordinate n (level form C(n, f)) but no unit within the
budget, n minimal; 'stuck' = neither within the budget.

Usage: python3 vreduce.py  (re-checks the FAIL lines of results.txt from mcensus)
"""
import heapq
import re

from mreduce import end_ms, l1, mk, sub_shift, width


def canon(v):
    a, b = v
    s = -a[0] if a[1] else -b[0]
    a = (a[0] + s, a[1]) if a[1] else a
    b = (b[0] + s, b[1]) if b[1] else b
    if (a[1] and a[1][0] < 0) or (not a[1] and b[1][0] < 0):
        a = (a[0], tuple(-x for x in a[1])) if a[1] else a
        b = (b[0], tuple(-x for x in b[1])) if b[1] else b
    return (a, b)


def vreduce(v, budget=20000, slack=2):
    v = canon(v)
    k0 = width(v[0]) + width(v[1])
    heap = [((k0, l1(v[0]) + l1(v[1])), v)]
    seen = {v}
    steps = 0
    const = float("inf")
    while heap and steps < budget:
        _, (a, b) = heapq.heappop(heap)
        steps += 1
        for x in (a, b):
            if len(x[1]) == 1 and abs(x[1][0]) == 1:
                return "unit", steps
        for x in (a, b):
            if len(x[1]) == 1:
                const = min(const, abs(x[1][0]))
        cands = []
        for m, k in end_ms(a, b):
            cands.append((sub_shift(a, b, m, k), b))
        for m, k in end_ms(b, a):
            cands.append((a, sub_shift(b, a, m, k)))
        for n in cands:
            if not n[0][1] or not n[1][1]:
                continue  # primitive vectors never reach a zero coordinate unless unimodular
            n = canon(n)
            if n in seen:
                continue
            kn = width(n[0]) + width(n[1])
            if kn > k0 + slack:
                continue
            seen.add(n)
            heapq.heappush(heap, ((kn, l1(n[0]) + l1(n[1])), n))
    if const < float("inf"):
        return "const %d" % const, steps
    return "stuck", steps


if __name__ == "__main__":
    counts = {}
    for line in open("results.txt"):
        mt = re.match(r"FAIL \(([-\d, ]+)\) \(([-\d, ]+)\) \(", line)
        if not mt:
            continue
        p = tuple(int(x) for x in mt.group(1).split(","))
        q = tuple(int(x) for x in mt.group(2).split(","))
        res, steps = vreduce((mk(p), mk([-x for x in q])))
        tag = res.split()[0]
        counts[tag] = counts.get(tag, 0) + 1
        print(p, q, res, steps)
    print("summary", counts)
