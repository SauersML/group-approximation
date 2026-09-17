#!/usr/bin/env python3
"""Rank-(2,4) bowties in [1,c]_W for rank n = 5 (labels in {2,3,5}, nondegenerate Tits form).

Usage: rank24_bowties.py <group> <height bound H> [cap]      (env CERT_OUT=file.json writes the first certificate;
       with CONTROL=1 and no certificate it writes an uncertified candidate, for a negative control of verify_bowtie24.py)

A rank-(2,4) bowtie: rank-2 elements x != y and coatoms u != v of [1,c]_W with x, y <= u, v, such that NO rank-3
element of [1,c]_W lies above both x and y.  Anything strictly between {x,y} and {u,v} has rank 3, so then u and v are
both minimal upper bounds of {x, y}, the join x v y does not exist, and [1,c]_W is not a lattice.

Exclusion.  A rank-3 z above x and y has Mov(z) containing U = Mov(x) + Mov(y) (lemma M1).  If dim U = 3 then
Mov(z) = U, and lemma D of the proof (det chi_c|Mov(z) > 0 for every z in [1,c]_W) excludes z whenever
det(E^T B (1-c)^{-1} E) <= 0 for a basis E of U.  (dim U = 4 cannot occur with u != v: it would force
Mov(u) = Mov(v) = U, and an element below c is determined by its moved space.)
Relations x <= u come from 2-letter subwords of 4-letter subwords of reduced reflection factorizations of c in the
bounded Hurwitz orbit (roots of height <= H).  Only lower bounds on the poset are used, so a certificate is valid for
any H, and 0 certificates at a bound proves nothing.
"""
import sys, itertools, time, os, json
from lattice_bowties import (setup, Ctx, hurwitz_orbit, z2q, qm_mul, qm_T, qm_rank, qsub, qadd, qmul, GROUPS)

def qsign(d):
    p, q = d
    if p >= 0 and q >= 0: return 1 if (p > 0 or q > 0) else 0
    if p <= 0 and q <= 0: return -1 if (p < 0 or q < 0) else 0
    if p > 0: return 1 if p * p > 5 * q * q else -1
    return 1 if 5 * q * q > p * p else -1

def det3(M):
    t = lambda a, b, c: qmul(qmul(a, b), c)
    s = t(M[0][0], M[1][1], M[2][2]); s = qadd(s, t(M[0][1], M[1][2], M[2][0])); s = qadd(s, t(M[0][2], M[1][0], M[2][1]))
    s = qsub(s, t(M[0][2], M[1][1], M[2][0])); s = qsub(s, t(M[0][0], M[1][2], M[2][1])); s = qsub(s, t(M[0][1], M[1][0], M[2][2]))
    return s

def main():
    name = sys.argv[1]; H = float(sys.argv[2]); cap = int(sys.argv[3]) if len(sys.argv) > 3 else 300000
    n, T = setup(name); assert n == 5
    ctx = Ctx(n, T); t0 = time.time()
    facts, closed = hurwitz_orbit(n, T, H, cap)
    facts = sorted(facts)
    print(f'[{name}] n={n} H={H}: {len(facts)} reduced reflection factorizations of c (bounded orbit closed: {closed})')
    pc = {}
    def P(letters):
        if letters not in pc: pc[letters] = ctx.prod(list(letters))
        return pc[letters]
    below = {}          # coatom -> set of rank-2 elements below it
    letters_of = {}     # rank-2 element -> its two letters (a basis of Mov)
    witness = {}        # (x, u) -> (f, S2, S4)
    for f in facts:
        for k in range(n):
            S4 = tuple(i for i in range(n) if i != k)
            u = P(tuple(f[i] for i in S4))
            bu = below.setdefault(u, set())
            for S2 in itertools.combinations(S4, 2):
                x = P(tuple(f[i] for i in S2))
                bu.add(x); letters_of.setdefault(x, (f[S2[0]], f[S2[1]]))
                witness.setdefault((x, u), (f, list(S2), list(S4)))
    print(f'  coatoms: {len(below)}; rank-2 elements: {len(letters_of)} [{time.time()-t0:.1f}s]')
    tops = {}
    for u, xs in below.items():
        for x, y in itertools.combinations(sorted(xs), 2):
            tops.setdefault((x, y), []).append(u)
    multi = {k: v for k, v in tops.items() if len(v) >= 2}
    print(f'  rank-2 pairs below >= 2 coatoms: {len(multi)} [{time.time()-t0:.1f}s]')
    stats = {}; certs = []
    for (x, y), us in multi.items():
        vecs = [[z2q(t) for t in r] for r in letters_of[x] + letters_of[y]]
        rk = qm_rank(vecs)
        if rk != 3:
            stats[f'dim U = {rk}'] = stats.get(f'dim U = {rk}', 0) + 1; continue
        basis = []
        for v in vecs:
            if qm_rank(basis + [v]) > len(basis): basis.append(v)
        Em = qm_T(basis)
        d = det3(qm_mul(qm_mul(qm_T(Em), ctx.chi), Em))
        s = qsign(d)
        key = 'det chi_c|U3 > 0' if s > 0 else 'det chi_c|U3 <= 0'
        stats[key] = stats.get(key, 0) + 1
        if s <= 0: certs.append((x, y, us[0], us[1], basis))
    print(f'  verdicts: {stats}')
    print(f'  CERTIFIED RANK-(2,4) BOWTIES: {len(certs)} [{time.time()-t0:.1f}s]')
    if os.environ.get('CERT_OUT') and not certs and os.environ.get('CONTROL') and multi:
        (x, y), us = next(iter(multi.items()))          # negative control: dump a candidate that is NOT certified
        certs = [(x, y, us[0], us[1], None)]
    if os.environ.get('CERT_OUT') and certs:
        x, y, u, v, basis = certs[0]
        json.dump({'group': name, 'n': n, 'edges': [[i, j, m] for (i, j), m in GROUPS[name][1].items()],
                   'x_letters': letters_of[x], 'y_letters': letters_of[y],
                   'u_witnesses': [witness[(x, u)], witness[(y, u)]], 'v_witnesses': [witness[(x, v)], witness[(y, v)]]},
                  open(os.environ['CERT_OUT'], 'w'), indent=1)
        print('  first certificate written to', os.environ['CERT_OUT'])
    return len(certs)

if __name__ == '__main__':
    main()
