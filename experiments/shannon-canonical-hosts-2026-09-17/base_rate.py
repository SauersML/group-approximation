#!/usr/bin/env python3
"""Base rate: among ALL configurations of the exhaustive scan (not only fakes), how many incidence patterns
force torsion by a two-letter certificate, and how many have a free or torsion-free one-relator host?

This measures whether the census in scan_*.txt is informative: if almost every pattern in a small finite
group forced torsion anyway, "every fake forces torsion" would say little.

usage: base_rate.py GROUP MAXE MAXF MAXN      (same enumeration as fake_hosts_scan.py; no LP is solved,
        except that MAXN filters by ground-set size exactly as the scan does)
"""
import sys, os, itertools, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
from shannon_lp import build
from random_scan import Cyc, Perm
from torsion2_scan import Z2k
from host_tietze import classify, power_root
from fake_hosts_scan import elements
from recheck_forced_torsion import forced


def main():
    name, maxE, maxF, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    if name.startswith('z') and name[1:].isdigit():
        n = int(name[1:]); G = Cyc(n); elems = list(range(n))
    elif name == 'k2':
        G = Z2k(2); elems = elements(G, [(1, 0), (0, 1)])
    elif name == 's3':
        G = Perm(3, None); elems = elements(G, [(1, 0, 2), (1, 2, 0)])
    others = [g for g in elems if g != G.one]
    counts = {}
    for kE in range(2, maxE + 1):
        for Er in itertools.combinations(others, kE - 1):
            E = [G.one] + list(Er)
            Einv = {G.inv(e) for e in E}
            for kF in range(2, maxF + 1):
                for F in itertools.combinations(elems, kF):
                    if not (Einv & set(F)):
                        continue
                    if build(G, E, list(F))['n'] > maxn:
                        continue
                    kind, names, alive, red, cert = classify(G, E, list(F))
                    tag = kind
                    if kind in ('ONE-REL-TOR', 'TORSION', 'UNKNOWN'):
                        good = bool(cert) and forced(G, E, list(F), names, cert[0])
                        rng = random.Random(0)
                        for _ in range(50):
                            if good:
                                break
                            _, names2, _, red2, _ = classify(G, E, list(F), rng)
                            good = any(k >= 2 and forced(G, E, list(F), names2, u)
                                       for u, k in (power_root(r) for r in red2))
                        tag = 'FORCED' if good else kind + '-uncertified'
                    counts[tag] = counts.get(tag, 0) + 1
    print('BASE %s maxE=%d maxF=%d maxn=%d: %s' % (name, maxE, maxF, maxn, counts), flush=True)


if __name__ == '__main__':
    main()
