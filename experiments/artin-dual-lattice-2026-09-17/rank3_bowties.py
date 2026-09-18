#!/usr/bin/env python3
"""Rank-(1,3) bowties in [1,c]_W, any rank n >= 4 (labels in {2,3,5}, nondegenerate Tits form).

Usage: rank3_bowties.py <group> <height bound H> [cap]      (env CERT_OUT=file.json writes the first certificate;
       with CONTROL=1 and no certificate it writes an uncertified candidate, for a negative control of verify_bowtie.py)

A rank-(1,3) bowtie: reflections a != b and rank-3 elements p != q of [1,c]_W with a, b <= p, q, such that NO
rank-2 element z of [1,c]_W lies above both a and b.  Then nothing lies strictly between {a,b} and {p,q}
(an element in between has rank 2), so a v b does not exist and [1,c]_W is not a lattice.

Exclusion of rank-2 elements above a, b (lemmas M1, M2): such a z has Mov(z) = U2 = span(alpha_a, alpha_b), z <= c in
O(V), hence z = z_U2 := 1 - E M^{-1} E^T B, M = E^T B (1-c)^{-1} E; and s_a z, s_b z are reflections of W.  So U2 is
excluded when M is singular, z_U2 is not over Z[phi], or s_a z_U2 / s_b z_U2 is certified not a reflection of W.
The script also records the sign of det(E^T B (1-c)^{-1} E); lemma D of the proof shows det <= 0 already excludes U2,
and this is the criterion verify_bowtie.py checks.  (On every run so far the two exclusion tests agree exactly.)
Relations a <= p come from 3-letter subwords of reduced reflection factorizations of c (Hurwitz orbit, roots of
height <= H).  Only lower bounds on the poset are used, so every certificate is valid whatever H is.
"""
import sys, itertools, time, os, json
from lattice_bowties import (setup, Ctx, hurwitz_orbit, z2q, q_in_zphi, qm_mul, qm_T, qsub, qmul, reflection_test, GROUPS)

def main():
    name = sys.argv[1]; H = float(sys.argv[2]); cap = int(sys.argv[3]) if len(sys.argv) > 3 else 300000
    n, T = setup(name); ctx = Ctx(n, T); t0 = time.time()
    facts, closed = hurwitz_orbit(n, T, H, cap)
    facts = sorted(facts)
    print(f'[{name}] n={n} H={H}: {len(facts)} reduced reflection factorizations of c (bounded orbit closed: {closed})')
    bad = sum(1 for f in facts[:3000] if ctx.prod(f) != ctx.c)
    assert bad == 0
    witness = {}; atoms_of = {}
    for f in facts:
        for S in itertools.combinations(range(n), 3):
            p = ctx.prod([f[i] for i in S])
            atoms_of.setdefault(p, set()).update(f[i] for i in S)
            for i in S: witness.setdefault((p, f[i]), (f, S))
    pair_tops = {}
    for p, ats in atoms_of.items():
        for a, b in itertools.combinations(sorted(ats), 2):
            pair_tops.setdefault((a, b), []).append(p)
    multi = {k: v for k, v in pair_tops.items() if len(v) >= 2}
    print(f'  rank-3 elements: {len(atoms_of)}; atom pairs below >= 2 rank-3 elements: {len(multi)} [{time.time()-t0:.1f}s]')
    stats = {}; certs = []
    for (a, b), ps in multi.items():
        E = [[z2q(x) for x in a], [z2q(x) for x in b]]
        Em = qm_T(E); M = qm_mul(qm_mul(qm_T(Em), ctx.chi), Em)
        detM = qsub(qmul(M[0][0], M[1][1]), qmul(M[0][1], M[1][0]))
        dsign = (lambda d: (d[0] > 0 and d[0]**2 > 5*d[1]**2) or (d[1] > 0 and 5*d[1]**2 > d[0]**2) or (d[0] > 0 and d[1] >= 0) or (d[1] > 0 and d[0] >= 0))(detM)
        dkey = 'det chi_c|U2 > 0' if dsign else 'det chi_c|U2 <= 0'
        stats[dkey] = stats.get(dkey, 0) + 1
        z = ctx.z_of_subspace(E)
        if z is None: why = 'M singular'
        elif not all(q_in_zphi(x) for row in z for x in row): why = 'z_U2 not over Z[phi]'
        else:
            Q = lambda m: [[z2q(x) for x in row] for row in m]
            ra = reflection_test(ctx, qm_mul(Q(ctx.R(a)), z))
            rb = reflection_test(ctx, qm_mul(Q(ctx.R(b)), z))
            if ra == 'no': why = 's_a z_U2 not a reflection'
            elif rb == 'no': why = 's_b z_U2 not a reflection'
            elif ra == rb == 'refl': why = None; stats['rank-2 candidate passes (s_a z, s_b z reflections of W)'] = stats.get('rank-2 candidate passes (s_a z, s_b z reflections of W)', 0) + 1
            else: why = None; stats['unknown'] = stats.get('unknown', 0) + 1
        if why:
            stats['certified: ' + why] = stats.get('certified: ' + why, 0) + 1
            certs.append((a, b, ps[0], ps[1], why))
            if dsign and why.startswith('s_'): stats['NOTE: reflection failure with det > 0'] = stats.get('NOTE: reflection failure with det > 0', 0) + 1
    print(f'  verdicts: {stats}')
    print(f'  CERTIFIED RANK-(1,3) BOWTIES: {len(certs)} [{time.time()-t0:.1f}s]')
    if os.environ.get('CERT_OUT') and not certs and os.environ.get('CONTROL') and multi:
        (a, b), ps = next(iter(multi.items()))          # negative control: dump a candidate that is NOT certified
        certs = [(a, b, ps[0], ps[1], 'control (not certified)')]
    if os.environ.get('CERT_OUT') and certs:
        a, b, p, q, why = certs[0]
        json.dump({'group': name, 'n': n, 'edges': [[i, j, m] for (i, j), m in GROUPS[name][1].items()],
                   'alpha_a': a, 'alpha_b': b,
                   'p_witnesses': [witness[(p, a)], witness[(p, b)]], 'q_witnesses': [witness[(q, a)], witness[(q, b)]],
                   'reason': why}, open(os.environ['CERT_OUT'], 'w'), indent=1)
        print('  first certificate written to', os.environ['CERT_OUT'])
    return len(certs)

if __name__ == '__main__':
    main()
