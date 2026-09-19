# For census lines: is the image of g in G^ab = Z^2 inside L = image of H?  (If not, a character
# trivial on H kills c: Lemma A.)  Also: the index of L, and the order of g-bar in Z^2/L.
import sys, ast
from collections import Counter
from fc import *
from nonab import *
import sympy as sp
C = Counter()
for line in open(sys.argv[1]):
    if '[' not in line: continue
    i = line.index('['); j = line.index(']') + 1
    E = [tuple(x) for x in ast.literal_eval(line[i:j])]
    rest = line[j:].split(); v0, v1, W = int(rest[0]), int(rest[1]), rest[2]
    key = line.split()[3]; key = 'bad' if key.startswith('bad') else key
    w = [LET.index(ch) for ch in W]; tr = mk(E)
    basis, c, g, tw = crow_words(E, tr, v0, v1, w)
    ab = lambda wd: (sum(DV[l][0] for l in wd), sum(DV[l][1] for l in wd))
    Lg = [ab(red(tw[E[e][0]] + [E[e][2]] + inv(tw[E[e][1]]))) for e in basis]
    M = sp.Matrix(Lg)
    from sympy.matrices.normalforms import smith_normal_form
    S = smith_normal_form(M, domain=sp.ZZ); inv_f = [abs(S[k, k]) for k in range(min(S.shape)) if S[k, k] != 0]
    gv = ab(g)
    # order of g-bar in Z^2/L: smallest d>0 with d*g in L (test d up to 50; 0 = infinite/large)
    def inL(v):
        A = sp.Matrix(Lg).T; sol = None
        try:
            from sympy.solvers.diophantine.diophantine import diophantine
        except Exception: pass
        # lattice membership via HNF of L
        import flint
        Hm = flint.fmpz_mat([list(r) for r in Lg] + [list(v)]).hnf()
        H0 = flint.fmpz_mat([list(r) for r in Lg]).hnf()
        return Hm.rank() == H0.rank() and all(Hm[k, k] == H0[k, k] for k in range(min(2, H0.rank())))
    d = next((d for d in range(1, 51) if inL((d * gv[0], d * gv[1]))), 0)
    C[(line.split()[0], key, 'L=' + str(inv_f), 'ord(g)=' + str(d))] += 1
for k, v in sorted(C.items()): print(v, k)
