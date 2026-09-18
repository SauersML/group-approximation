"""Search for Y in E_2(R), R = Z[t,t^-1], with Y v = +-w for primitive vectors v, w.

If Y v = +-w then C(v) = Y^{-1} C(w) Y (proof node
sl2-laurent-elementary-iff-three-unipotent-conditions-proof, Lemma 3, and C(-w) = C(w)),
so C(v) is elementary iff C(w) is.  States are taken modulo diag(t^k, t^-k) (which lies
in E_2) and sign, but NOT modulo scaling v by a unit, which changes C(v) to u(t^{2k}; v).

Usage: python3 vorbit.py budget slack  p0,p1,.. q0,q1,..  P0,P1,.. Q0,Q1,..
(vectors (p, -q) and (P, -Q) with coefficient lists starting at degree 0).
Failure is evidence only.
"""
import heapq
import sys

from mreduce import end_ms, l1, mk, sub_shift, width


def canon(v):
    a, b = v
    k = a[0]
    a = (0, a[1])
    b = (b[0] + k, b[1])
    if a[1][0] < 0:
        a = (a[0], tuple(-x for x in a[1]))
        b = (b[0], tuple(-x for x in b[1]))
    return (a, b)


def vorbit(v, w, budget=100000, slack=2):
    v, w = canon(v), canon(w)
    k0 = width(v[0]) + width(v[1])
    heap = [((k0, l1(v[0]) + l1(v[1])), v)]
    seen = {v}
    steps = 0
    while heap and steps < budget:
        _, (a, b) = heapq.heappop(heap)
        steps += 1
        if (a, b) == w:
            return True, steps
        cands = []
        for m, k in end_ms(a, b):
            cands.append((sub_shift(a, b, m, k), b))
        for m, k in end_ms(b, a):
            cands.append((a, sub_shift(b, a, m, k)))
        for n in cands:
            if not n[0][1] or not n[1][1]:
                continue
            n = canon(n)
            if n in seen:
                continue
            kn = width(n[0]) + width(n[1])
            if kn > k0 + slack:
                continue
            seen.add(n)
            heapq.heappush(heap, ((kn, l1(n[0]) + l1(n[1])), n))
    return False, steps


if __name__ == "__main__":
    budget, slack = int(sys.argv[1]), int(sys.argv[2])
    p, q, P, Q = ([int(x) for x in s.split(",")] for s in sys.argv[3:7])
    v = (mk(p), mk([-x for x in q]))
    w = (mk(P), mk([-x for x in Q]))
    print(p, q, "->", P, Q, "budget", budget, "slack", slack, vorbit(v, w, budget, slack))
