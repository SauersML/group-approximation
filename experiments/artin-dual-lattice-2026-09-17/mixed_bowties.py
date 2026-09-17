#!/usr/bin/env python3
"""Mixed-rank non-join certificates in [1,c]_W, n = 5: reflections a != b, a rank-3 element p and a coatom u of
[1,c]_W with a, b <= p, a, b <= u, det chi_c|span(alpha_a, alpha_b) <= 0 and Mov(p) not contained in Mov(u).

Usage: mixed_bowties.py <group> <height bound H> [cap]

Why this certifies non-lattice: by lemma D no rank-2 element lies above a and b, so every upper bound of {a, b} has
rank >= 3.  If a v b existed it would lie below p, have rank >= 3 = rank p, hence equal p; and p <= u would force
Mov(p) <= Mov(u) (lemma M1).  So a v b does not exist.
Relations come from 3- and 4-letter subwords of reduced reflection factorizations of c in the bounded Hurwitz orbit.
Only lower bounds on the poset are used; 0 certificates at a bound proves nothing.
Diagnostics: a pair of letters that occur in one factorization has the 2-subword above it, so det > 0 there
(lemma D); the pairs examined are those below a common rank-3 element that never occur together in a factorization.
"""
import sys, itertools, time
from lattice_bowties import (setup, Ctx, hurwitz_orbit, z2q, qm_mul, qm_T, qm_rank, qsub, qmul)
from rank24_bowties import qsign

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
    atoms3, letters3, atoms4, letters4 = {}, {}, {}, {}
    cooccur = set()
    for f in facts:
        for i, j in itertools.combinations(range(n), 2): cooccur.add(tuple(sorted((f[i], f[j]))))
        for S in itertools.combinations(range(n), 3):
            p = P(tuple(f[i] for i in S)); atoms3.setdefault(p, set()).update(f[i] for i in S); letters3.setdefault(p, [f[i] for i in S])
        for S in itertools.combinations(range(n), 4):
            u = P(tuple(f[i] for i in S)); atoms4.setdefault(u, set()).update(f[i] for i in S); letters4.setdefault(u, [f[i] for i in S])
    ups4 = {}
    for u, ats in atoms4.items():
        for a in ats: ups4.setdefault(a, set()).add(u)
    print(f'  rank-3 elements: {len(atoms3)}; coatoms: {len(atoms4)} [{time.time()-t0:.1f}s]')
    pairs = {}
    for p, ats in atoms3.items():
        for a, b in itertools.combinations(sorted(ats), 2):
            if (a, b) not in cooccur: pairs.setdefault((a, b), []).append(p)
    print(f'  atom pairs below a rank-3 element, never in one factorization: {len(pairs)} [{time.time()-t0:.1f}s]')
    stats = {}; certs = []
    for (a, b), ps in pairs.items():
        Em = qm_T([[z2q(x) for x in a], [z2q(x) for x in b]])
        M = qm_mul(qm_mul(qm_T(Em), ctx.chi), Em)
        s = qsign(qsub(qmul(M[0][0], M[1][1]), qmul(M[0][1], M[1][0])))
        if s > 0:
            stats['det > 0'] = stats.get('det > 0', 0) + 1; continue
        stats['det <= 0'] = stats.get('det <= 0', 0) + 1
        if len(ps) >= 2: stats['det <= 0, >= 2 rank-3 above (rank-(1,3) bowtie)'] = stats.get('det <= 0, >= 2 rank-3 above (rank-(1,3) bowtie)', 0) + 1
        us = ups4.get(a, set()) & ups4.get(b, set())
        if len(ps) == 1:
            inside = sum(1 for u in us if qm_rank([[z2q(x) for x in r] for r in letters4[u] + letters3[ps[0]]]) == 4)
            print(f'    det <= 0 pair with one rank-3 element above: coatoms above a, b: {len(us)}, containing Mov(p): {inside}')
        for p in ps:
            for u in us:
                if qm_rank([[z2q(x) for x in r] for r in letters4[u] + letters3[p]]) > 4:
                    certs.append((a, b, p, u)); break
            else: continue
            break
    print(f'  verdicts: {stats}')
    print(f'  CERTIFIED MIXED (1; 3, 4) NON-JOINS: {len(certs)} [{time.time()-t0:.1f}s]')
    return len(certs)

if __name__ == '__main__':
    main()
