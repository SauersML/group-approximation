import sys
from tp import M, census_rules, SHAPES
from census_moves import shape_sets, residuals, TORS
from i0_path import path
from i0_dp import min_conflicts
from level2b import close, feasible
# Class I_0. For every rule: which swaps (Lemma 3.1) and which cycles with no equalities imposed exist.
# Rules whose path conflict sets are torsion labels only are closed exactly as in level2b.
LAB = set(TORS.values())
if __name__ == '__main__':
    stats = {}
    n = nclosed = ntors = 0
    for key, mu, B in census_rules():
        double = [(i, j) for i, j in [(0, 1), (0, 2), (1, 2)] if B[i] & B[j]]
        if not double or any(shape_sets(mu, m, m2) for m, m2 in SHAPES):
            continue
        n += 1
        sets = []
        for i, j in double:
            S, winsites, sites = path(i, j, 3 - i - j)
            sets += min_conflicts(mu, S, winsites)
        others = lambda r: {'%s2' % e for e in 'abc' if e != r[0]}
        moves = tuple(r.replace('2', '-swap').replace('3', '-cycle') for r in ['a2', 'b2', 'c2', 'a3', 'b3', 'c3']
                      if feasible(mu, r, others(r)))
        if sets and all(F <= LAB for F in sets):
            ntors += 1
            memo = {}
            outs = []
            for R in residuals(sets):
                used, bad = close(mu, frozenset(R), memo)
                outs.append('%s:%s' % (','.join(sorted(R)), '+'.join(used) if used else 'OPEN@' + ','.join(sorted(bad))))
            nclosed += not any('OPEN' in o for o in outs)
            verdict = ('torsion-only path sets',) + tuple(outs)
        else:
            verdict = ('path sets carry other relators',)
        tag = (key[0], '+'.join((M[i] or '1') + M[j] for i, j in double), moves, verdict)
        stats.setdefault(tag, []).append(key)
        if n % 20 == 0:
            print('progress', n, file=sys.stderr, flush=True)
    for tag in sorted(stats, key=str):
        print(len(stats[tag]), tag, 'eg', stats[tag][0], flush=True)
    print('I_0 rules', n, 'torsion-only', ntors, 'closed', nclosed)
