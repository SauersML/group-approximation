# Candidate 1 (census2 4 4 4 2 1 80): tests of the abelianized row, finite permutation representations
# of degree <= KMAX, and the g in P shadow in each of them.
import sys
from fc import *
from nonab import *
from sympy.combinatorics import Permutation, PermutationGroup
E = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (2, 1, 0), (2, 2, 1), (3, 2, 0), (3, 3, 1)]
W = 'yXyXyxYxYXXyyxxYXyXyxYxYYYXXyyxYYx'; w = [LET.index(ch) for ch in W]
tr = mk(E); v0, v1 = 0, 1
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
basis, c, g, tw = crow_words(E, tr, v0, v1, w)
b2, cab, gab = crow_ab(E, tr, v0, v1, w)
assert b2 == basis
# abelian image check (per-coordinate unit tau_{o(e)} is absent in both conventions)
for bi, e in enumerate(basis):
    p = {}
    for sg, wd in c[e]:
        m = (sum(DV[l][0] for l in wd), sum(DV[l][1] for l in wd)); p[m] = p.get(m, 0) + sg
        if p[m] == 0: del p[m]
    assert p == cab[bi], (e, p, cab[bi])
print('abelian image agrees; basis', basis, 'g =', ''.join(LET[l] for l in g))
print('z_unit', z_unit(cab))
# generators of H: basis loops tau_o e tau_t^-1
Hgens = []
for e in basis:
    a, b, m = E[e]; Hgens.append(red(tw[a] + [m] + inv(tw[b])))
print('H basis', [''.join(LET[l] for l in h) for h in Hgens])
PR = (2, 3, 5, 7, 11, 13, 10007)
for k in range(2, KMAX + 1):
    nrep = 0; kills = []; gP = 0
    for X, Y in reps(w, k):
        nrep += 1
        for p in PR:
            r = row_rank(c, basis, X, Y, k, p)
            if r < k: kills.append((X, Y, p, r)); break
        Gp = Permutation(perm_word(X, Y, g, k)); Hp = [Permutation(perm_word(X, Y, h, k)) for h in Hgens]
        o = Gp.order(); conj = [Gp ** j * h * Gp ** (-j) for j in range(o) for h in Hp]
        if PermutationGroup(conj).contains(Gp): gP += 1
    print('degree', k, 'transitive reps', nrep, 'killing', len(kills), 'g in P-shadow', gP, flush=True)
    for K in kills[:5]: print('   kill', K)
