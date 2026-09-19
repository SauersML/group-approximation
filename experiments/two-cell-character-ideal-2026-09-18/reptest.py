# Filter ZUNIT census lines through permutation representations of degree <= KMAX.
# usage: python3 reptest.py census_file KMAX
import sys, ast
from fc import *
from nonab import *
from sympy.combinatorics import Permutation, PermutationGroup
PR = (2, 3, 5, 7, 11, 13, 10007)
KMAX = int(sys.argv[2])
for line in open(sys.argv[1]):
    if 'ZUNIT' not in line: continue
    i = line.index('['); j = line.index(']') + 1
    E = [tuple(e) for e in ast.literal_eval(line[i:j])]
    rest = line[j:].split(); v0, v1, W = int(rest[0]), int(rest[1]), rest[2]
    w = [LET.index(ch) for ch in W]; tr = mk(E)
    basis, c, g, tw = crow_words(E, tr, v0, v1, w)
    Hgens = [red(tw[E[e][0]] + [E[e][2]] + inv(tw[E[e][1]])) for e in basis]
    out = []; dead = None
    for k in range(2, KMAX + 1):
        nrep = 0; gP = 0
        for X, Y in reps(w, k):
            nrep += 1
            for p in PR:
                if row_rank(c, basis, X, Y, k, p) < k: dead = (k, p, X, Y); break
            if dead: break
            Gp = Permutation(perm_word(X, Y, g, k)); Hp = [Permutation(perm_word(X, Y, h, k)) for h in Hgens]
            conj = [Gp ** jj * h * Gp ** (-jj) for jj in range(Gp.order()) for h in Hp]
            if PermutationGroup(conj).contains(Gp): gP += 1
        out.append((k, nrep, gP))
        if dead: break
    print('KILLED' if dead else 'SURVIVES', dead, out, line.split()[:3], E, v0, v1, W, flush=True)
