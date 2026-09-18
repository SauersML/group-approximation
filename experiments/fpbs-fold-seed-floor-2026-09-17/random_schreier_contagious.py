"""Sanity check: small 2-of-3 contagious sets on random permutation actions of F_2.

Triples T_v = (v, a v, b v) counted with multiplicity. A greedy heuristic adds
the seed that maximises the closure growth among a random sample, until the
closure is everything. It gives an UPPER bound on the minimal contagious
density of that finite action; the theorem in
research/fpbs-weakly-bernoulli-fold-seeds-have-density-floor.md gives the
LOWER bound 1/80 asymptotically. We also report, for the final seed set, the
largest number of spanned slots of the infected set at the crossing size n/8,
to illustrate the counting identity slots >= 2(|I| - |S|).
"""
import random
import sys


def closure(n, A, B, seeds, inv_trip):
    inf = bytearray(n)
    cnt = [0] * n  # infected slots of triple v
    order = []
    stack = []
    for s in seeds:
        if not inf[s]:
            inf[s] = 1
            stack.append(s)
            order.append(s)
    while stack:
        u = stack.pop()
        for (t, mult) in inv_trip[u]:
            cnt[t] += mult
            if cnt[t] >= 2:
                for w in (t, A[t], B[t]):
                    if not inf[w]:
                        inf[w] = 1
                        stack.append(w)
                        order.append(w)
    return inf, order


def build(n, rng):
    A = list(range(n)); rng.shuffle(A)
    B = list(range(n)); rng.shuffle(B)
    inv = [dict() for _ in range(n)]
    for v in range(n):
        for w in (v, A[v], B[v]):
            inv[w][v] = inv[w].get(v, 0) + 1
    inv_trip = [list(d.items()) for d in inv]
    return A, B, inv_trip


def greedy(n, rng, sample=40):
    A, B, inv_trip = build(n, rng)
    seeds = []
    inf, order = closure(n, A, B, seeds, inv_trip)
    while len(order) < n:
        cand = [v for v in rng.sample(range(n), min(n, 4 * sample)) if not inf[v]][:sample]
        best, bestsz = None, -1
        for c in cand:
            _, o = closure(n, A, B, seeds + [c], inv_trip)
            if len(o) > bestsz:
                best, bestsz = c, len(o)
        seeds.append(best)
        inf, order = closure(n, A, B, seeds, inv_trip)
    # slots spanned at crossing size n/8 along the sequential order
    m = n // 8
    I = set(order[:m])
    slots = sum((A[v] in I) + (B[v] in I) for v in I)
    s_in = len(set(seeds) & I)
    return len(seeds) / n, m, slots, s_in


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 917)
    for n in (500, 1000, 2000):
        dens, m, slots, s_in = greedy(n, rng)
        print("n=%d greedy contagious density=%.4f  crossing m=%d slots=%d "
              ">= 2(m-|S cap I|)=%d  (1.8 m = %.0f)"
              % (n, dens, m, slots, 2 * (m - s_in), 1.8 * m))
