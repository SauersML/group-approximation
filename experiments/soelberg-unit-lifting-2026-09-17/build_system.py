#!/usr/bin/env python3
"""Characteristic-zero lifting system for Gardam's Soelberg unit support pair (A, B).

u = sum_i u_i A_i, v = sum_j v_j B_j, u v = 1 in K[S]: one bilinear equation per group element in A B.
Gardam-style localization: case (i, j) means u_k = 0 for k < j, k != i, u_i = 1 and u_j != 0 (w u_j = 1).
Every nontrivial unit supported in (A, B) falls in exactly one case (a unit with |supp u| = 1 is trivial).

Combinatorial pruning (characteristic free): in case (i, j) the actual supports A' subset A, B' subset B
must satisfy, for every group element g != 1, #{(k, l) in A' x B' : A_k B_l = g} != 1 (otherwise
u_k v_l = 0 for a pair of support elements), and at least one pair at the identity. Cases for which
this SAT instance is UNSAT carry no unit; the rest are written as msolve input files.

usage: python3 build_system.py [outdir]
"""
import sys, os, itertools
from soelberg_engine import A, B, I3, product_table
from pysat.solvers import Cadical153

N = len(A)
TAB = product_table(A, B)
ELEMS = list(TAB.keys())

def uvar(i):
    return 'u%d' % (i + 1)

def vvar(j):
    return 'v%d' % (j + 1)

def equations():
    eqs = []
    for g in ELEMS:
        terms = ['%s*%s' % (uvar(i), vvar(j)) for (i, j) in TAB[g]]
        s = '+'.join(terms)
        if g == I3:
            s += '-1'
        eqs.append(s)
    return eqs

def sat_case(i, j, forbid_full=False):
    """SAT: is there (A', B') with i, j in A', k not in A' for k < j (k != i), satisfying the
    no-unique-product condition?  Returns a model (A', B') or None."""
    s_ = lambda k: k + 1
    t_ = lambda l: N + l + 1
    nxt = [2 * N + 1]
    def new():
        nxt[0] += 1
        return nxt[0] - 1
    clauses = []
    pv = {}
    for g in ELEMS:
        for (k, l) in TAB[g]:
            p = new()
            pv[(k, l)] = p
            clauses += [[-p, s_(k)], [-p, t_(l)], [p, -s_(k), -t_(l)]]
    for g in ELEMS:
        ps = [pv[kl] for kl in TAB[g]]
        if g == I3:
            clauses.append(ps)
        else:
            for p in ps:
                clauses.append([-p] + [q for q in ps if q != p])
    clauses.append([s_(i)])
    clauses.append([s_(j)])
    for k in range(j):
        if k != i:
            clauses.append([-s_(k)])
    with Cadical153(bootstrap_with=clauses) as solver:
        if solver.solve():
            m = set(x for x in solver.get_model() if x > 0)
            return ([k for k in range(N) if s_(k) in m], [l for l in range(N) if t_(l) in m])
    return None

def msolve_case(i, j, char=1000000007, both_sides=True):
    zero = [k for k in range(j) if k != i]
    vars_u = [uvar(k) for k in range(N) if k not in zero]
    vars_all = vars_u + [vvar(l) for l in range(N)] + ['w']
    polys = []
    for g in ELEMS:
        terms = []
        for (k, l) in TAB[g]:
            if k in zero:
                continue
            if k == i:
                terms.append(vvar(l))
            else:
                terms.append('%s*%s' % (uvar(k), vvar(l)))
        s = '+'.join(terms) if terms else '0'
        if g == I3:
            s += '-1'
        if s != '0':
            polys.append(s)
    if both_sides:
        # v u = 1 as well (redundant over a field, since K[S] is directly finite, but it helps the F4 run)
        tab2 = product_table(B, A)
        for g, pairs in tab2.items():
            terms = []
            for (l, k) in pairs:
                if k in zero:
                    continue
                terms.append(vvar(l) if k == i else '%s*%s' % (vvar(l), uvar(k)))
            s = '+'.join(terms) if terms else '0'
            if g == I3:
                s += '-1'
            if s != '0':
                polys.append(s)
    polys.append('%s*w-1' % uvar(j))
    # u_i = 1 is substituted; drop u_i from variables
    vars_all = [x for x in vars_all if x != uvar(i)]
    return ','.join(vars_all) + '\n' + str(char) + '\n' + ',\n'.join(polys) + '\n'

if __name__ == '__main__':
    outdir = sys.argv[1] if len(sys.argv) > 1 else 'cases'
    os.makedirs(outdir, exist_ok=True)
    viable = []
    for i in range(N):
        for j in range(i + 1, N):
            m = sat_case(i, j)
            if m is not None:
                viable.append((i, j))
                with open(os.path.join(outdir, 'case_%02d_%02d.ms' % (i + 1, j + 1)), 'w') as f:
                    f.write(msolve_case(i, j))
    print('equations:', len(ELEMS))
    print('cases total:', N * (N - 1) // 2, ' SAT-viable cases:', len(viable))
    print('viable (1-based):', [(i + 1, j + 1) for (i, j) in viable])
