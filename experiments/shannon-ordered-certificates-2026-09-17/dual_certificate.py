#!/usr/bin/env python3
"""Print the dual certificate (nonzero elemental-inequality multipliers) of a minimal-window LP.

usage: dual_certificate.py z 'E' 'F'     e.g. dual_certificate.py z 0,1,2 -2,-1,0
       dual_certificate.py f 'E' 'F'     words in a,b,A,B; '1' is the identity
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'shannon-window-certificates-2026-09-17'))
from scipy.optimize import linprog
from shannon_lp import Zd, Free, build, constraints, objective


def parse(kind, s):
    if kind == 'z':
        return [(int(t),) for t in s.split(',')]
    return ['' if t == '1' else t for t in s.split(',')]


def name(d, m):
    out = []
    for i, (k, g) in enumerate(d['items']):
        if m >> i & 1:
            out.append('%s%s' % (k, d['G'].show(g)))
    return ''.join('[' + t + ']' for t in out) if out else '{}'


def main():
    kind, E, F = sys.argv[1], sys.argv[2], sys.argv[3]
    G = Zd(1) if kind == 'z' else Free
    E, F = parse(kind, E), parse(kind, F)
    d = build(G, E, F)
    A_ub, b_ub, A_eq, b_eq, desc = constraints(d)
    c = objective(d)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs-ds')
    print('n=%d nv=%d LP=%.9f' % (d['n'], d['nv'], res.fun))
    mu = res.ineqlin.marginals
    terms = [(abs(v), v, desc[i]) for i, v in enumerate(mu) if abs(v) > 1e-9]
    terms.sort(key=lambda t: -t[0])
    for _, v, ds in terms:
        if ds[0] == 'mono':
            print('%+.4f  mono  H(all) >= H(all - %s)' % (-v, name(d, 1 << ds[1])))
        else:
            _, i, j, K = ds
            print('%+.4f  I(%s ; %s | %s) >= 0' % (-v, name(d, 1 << i), name(d, 1 << j), name(d, K)))


if __name__ == '__main__':
    main()
