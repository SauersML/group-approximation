# Unimodularity of the cylinder row over Z[Q] for finite quotients Q of G (images of transitive
# permutation representations of degree <= KMAX, |Q| <= QMAX), via the Hermite normal form of the
# regular representation: c is unimodular over Z[Q] iff the columns of [L(c_1) ... L(c_B)] span Z^Q.
# usage: python3 zq.py census_line_file KMAX QMAX
import sys, ast, flint
from fc import *
from nonab import *


def closure(X, Y, k):
    e = tuple(range(k)); gens = [tuple(X), tuple(Y)]
    el = {e: 0}; L = [e]; i = 0
    while i < len(L):
        u = L[i]; i += 1
        for gg in gens:
            v = tuple(gg[u[j]] for j in range(k))      # u then gg
            if v not in el: el[v] = len(L); L.append(v)
    return el, L


def zq_unimodular(c, basis, X, Y, k, QMAX):
    el, L = closure(X, Y, k); n = len(L)
    if n > QMAX: return None, n
    M = [[0] * (len(basis) * n) for _ in range(n)]
    for bi, e in enumerate(basis):
        for sg, wd in c[e]:
            q = tuple(perm_word(X, Y, wd, k))
            for hj, h in enumerate(L):
                qh = tuple(h[q[j]] for j in range(k))   # q then h = q*h
                M[el[qh]][bi * n + hj] += sg
    H = flint.fmpz_mat(M).transpose().hnf()
    d = 1
    for i in range(n): d *= int(H[i, i])
    return abs(d) == 1, n


if __name__ == "__main__":
    KMAX = int(sys.argv[2]); QMAX = int(sys.argv[3])
    for line in open(sys.argv[1]):
        i = line.index('['); j = line.index(']') + 1
        E = [tuple(x) for x in ast.literal_eval(line[i:j])]
        rest = line[j:].split(); v0, v1, W = int(rest[0]), int(rest[1]), rest[2]
        w = [LET.index(ch) for ch in W]; tr = mk(E)
        basis, c, g, tw = crow_words(E, tr, v0, v1, w)
        seen = set(); res = {}
        for k in range(2, KMAX + 1):
            for X, Y in reps(w, k):
                el, L = closure(X, Y, k)
                if len(L) > QMAX: continue
                ok, n = zq_unimodular(c, basis, X, Y, k, QMAX)
                res.setdefault(n, [0, 0])[0 if ok else 1] += 1
                if not ok: print('  NOT unimodular over Z[Q], |Q| =', n, 'X', X, 'Y', Y, flush=True)
        print(W, 'order: [unimodular, not]', sorted(res.items()), flush=True)
