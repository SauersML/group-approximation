#!/usr/bin/env python3
"""Directed search for gap tables of shape ns x N inside BS(p,q), through the coincidence graph of S.

For a fixed memory S (1 in S), the *coincidence graph* has an edge m -- m' whenever s m = s' m' for some s != s' in S,
that is m' = s'^-1 s m. The coincidences of T_f(S, M) are exactly the induced edges on M. A non-identity label of M
that lies on no induced edge stays a free letter of P(T), so a table with P(T) = BS(p,q) through two alive letters
needs every such label on an induced edge. This search only tries the M that are *connected* in the induced graph and
contain 1. It enumerates them with the ESU algorithm rooted at 1, so each set is visited once. Each M is kept when the
number of coincidences is at least ns + N - 3, some reverse pair is distinct in G and equal in H, and
gaptable.certify_iso certifies P(T) = BS(p,q) through the labels.

usage: schreiersearch.py p q RS ns N out.jsonl [maxhits] [S-words comma separated, fixed S]
"""
import itertools
import json
import sys
import time

from bsgroup import BS, ball, wstr
from gaptable import certify_iso

LET = {'a': 1, 'A': -1, 't': 2, 'T': -2}


def parse(w):
    return [] if w == '1' else [LET[c] for c in w]


def run_S(G, Sw, N, out, maxhits, stats):
    one = G.nf([])
    ns = len(Sw)
    words = {one: []}

    def nbrs(k):
        w = words[k]
        res = []
        for si in range(ns):
            for sj in range(ns):
                if si != sj:
                    v = [-x for x in reversed(Sw[sj])] + Sw[si] + w
                    kk = G.nf(v)
                    if kk not in words:
                        words[kk] = v
                    res.append(kk)
        return res
    nb_cache = {}

    def N_(k):
        if k not in nb_cache:
            nb_cache[k] = [x for x in set(nbrs(k)) if x != k]
        return nb_cache[k]
    need = ns + N - 3
    hits = 0

    def test(sub):
        nonlocal hits
        stats['tested'] += 1
        Mw = [words[k] for k in sub]
        classes = {}
        for si in range(ns):
            for mi in range(N):
                classes.setdefault(G.nf(Sw[si] + Mw[mi]), []).append(0)
        coinc = ns * N - len(classes)
        if coinc < need:
            return
        stats['enough_coincidences'] += 1
        cells = [(mi, si) for mi in range(N) for si in range(ns)]
        rk = {c: G.nf(Mw[c[0]] + Sw[c[1]]) for c in cells}
        rh = {c: G.rfq(Mw[c[0]] + Sw[c[1]]) for c in cells}
        gaps = [(c, d) for c, d in itertools.combinations(cells, 2) if rh[c] == rh[d] and rk[c] != rk[d]]
        if not gaps:
            return
        stats['with_gap_pair'] += 1
        rec = certify_iso(G, Sw, Mw, gaps)
        if rec:
            hits += 1
            stats['certified'] += 1
            out.write(json.dumps(rec) + '\n')
            out.flush()

    # ESU rooted at one (the root is the only vertex compared by index, and it is minimal)
    def extend(sub, ext, nbhd):
        if hits >= maxhits:
            return
        if len(sub) == N:
            test(sub)
            return
        ext = list(ext)
        while ext:
            w = ext.pop()
            new = [u for u in N_(w) if u not in nbhd]
            nb2 = set(nbhd)
            nb2.update(new)
            extend(sub + [w], ext + new, nb2)
            if hits >= maxhits:
                return
    root_n = N_(one)
    extend([one], root_n, set([one] + root_n))
    return hits


def main():
    p, q, RS, ns, N = map(int, sys.argv[1:6])
    outp = sys.argv[6]
    maxhits = int(sys.argv[7]) if len(sys.argv) > 7 else 5
    G = BS(p, q)
    stats = {'tested': 0, 'enough_coincidences': 0, 'with_gap_pair': 0, 'certified': 0, 'S_tried': 0, 'S_with_hit': 0}
    t0 = time.time()
    if len(sys.argv) > 8:
        Slist = [[parse(w) for w in sys.argv[8].split(',')]]
    else:
        B = ball(G, RS)
        one = G.nf([])
        others = [B[k] for k in B if k != one]
        Slist = [[[]] + list(c) for c in itertools.combinations(others, ns - 1)]
    with open(outp, 'w') as out:
        for Sw in Slist:
            stats['S_tried'] += 1
            h = run_S(G, Sw, N, out, maxhits, stats)
            if h:
                stats['S_with_hit'] += 1
    stats.update({'p': p, 'q': q, 'RS': RS, 'ns': ns, 'N': N, 'sec': round(time.time() - t0, 1)})
    print(json.dumps(stats))


if __name__ == '__main__':
    main()
