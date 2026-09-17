#!/usr/bin/env python3
"""Exhaustive directed search for gap tables inside BS(p,q) over a ball.

All pairs (S, M) of subsets of the ball of radius R containing 1, |S| = ns, |M| = nm, are tested with
gaptable.certify: a reverse pair distinct in G but equal in the largest residually finite quotient, and a
Tietze certificate that the table group P(T_f(S, M)) is BS(p,q) through the labels.

usage: bsgapsearch.py p q R ns nm out.jsonl [maxhits]
"""
import itertools
import json
import sys
import time

from bsgroup import BS, ball
from gaptable import certify


def main():
    p, q, R, ns, nm = map(int, sys.argv[1:6])
    out = sys.argv[6]
    maxhits = int(sys.argv[7]) if len(sys.argv) > 7 else 50
    G = BS(p, q)
    B = ball(G, R)
    one = G.nf([])
    others = [B[k] for k in B if k != one]
    n = len(B)
    # precompute reverse products (element and residually finite image) to discard pairs without a gap pair fast
    words = [[]] + others
    E, H = {}, {}
    rk = [[E.setdefault(G.nf(words[i] + words[j]), len(E)) for j in range(n)] for i in range(n)]
    rh = [[H.setdefault(G.rfq(words[i] + words[j]), len(H)) for j in range(n)] for i in range(n)]
    t0 = time.time()
    hits = tested = gapped = 0
    with open(out, 'w') as f:
        for Sr in itertools.combinations(range(1, n), ns - 1):
            S = (0,) + Sr
            for Mr in itertools.combinations(range(1, n), nm - 1):
                M = (0,) + Mr
                tested += 1
                seen = {}
                g = False
                for m in M:
                    for s in S:
                        h, e = rh[m][s], rk[m][s]
                        st = seen.setdefault(h, set())
                        if st and e not in st:
                            g = True
                        st.add(e)
                if not g:
                    continue
                gapped += 1
                rec = certify(G, [words[i] for i in S], [words[i] for i in M])
                if rec:
                    hits += 1
                    f.write(json.dumps(rec) + '\n')
                    if hits >= maxhits:
                        break
            if hits >= maxhits:
                break
    print(json.dumps({'p': p, 'q': q, 'R': R, 'ns': ns, 'nm': nm, 'ball': n, 'tested': tested,
                      'with_gap_pair': gapped, 'certified_gap_tables': hits, 'sec': round(time.time() - t0, 1)}))


if __name__ == '__main__':
    main()
