#!/usr/bin/env python3
"""Extend a base pair (S0, M0) in BS(p,q) by elements of the ball of radius R and certify gap tables.

usage: extend.py p q R S0 M0 ns nm out.jsonl
   S0, M0: comma-separated words over a A t T, '1' for the identity (must come first).
"""
import itertools, json, sys, time
from bsgroup import BS, ball
from gaptable import certify

def parse(s):
    d = {'a': 1, 'A': -1, 't': 2, 'T': -2}
    return [[d[c] for c in w] if w != '1' else [] for w in s.split(',')]

def main():
    p, q, R = map(int, sys.argv[1:4])
    S0, M0 = parse(sys.argv[4]), parse(sys.argv[5])
    ns, nm = int(sys.argv[6]), int(sys.argv[7])
    G = BS(p, q)
    B = ball(G, R)
    S0k = {G.nf(w) for w in S0}; M0k = {G.nf(w) for w in M0}
    cS = [B[k] for k in B if k not in S0k]
    cM = [B[k] for k in B if k not in M0k]
    t0 = time.time(); hits = 0; tested = 0
    with open(sys.argv[8], 'w') as f:
        for es in itertools.combinations(cS, ns - len(S0)):
            for em in itertools.combinations(cM, nm - len(M0)):
                tested += 1
                rec = certify(G, S0 + list(es), M0 + list(em))
                if rec:
                    hits += 1
                    f.write(json.dumps(rec) + '\n')
    print(json.dumps({'base': sys.argv[4:6], 'R': R, 'shape': [ns, nm], 'tested': tested, 'hits': hits, 'sec': round(time.time() - t0, 1)}))

main()
