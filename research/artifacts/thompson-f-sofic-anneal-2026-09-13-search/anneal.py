#!/usr/bin/env python3
# Heuristic search: pairs (A,B) in Sym(n) that nearly satisfy the two Thompson F relators
#   R1 = [a b^-1, a^-1 b a],  R2 = [a b^-1, a^-2 b a^2]
# while keeping the commutator d(AB, BA) >= eps.  Output: best relator defect found.
# Upper bounds only; this cannot certify stability or soficity.
import sys, json, numpy as np

def inv(p):
    q = np.empty_like(p); q[p] = np.arange(len(p)); return q

def word(letters):
    # letters: list of (gen, sign); returns tokens
    return letters

def comm(x, y):  # [x,y] = x^-1 y^-1 x y  (x,y are token lists)
    xi = [(g, -s) for g, s in reversed(x)]
    yi = [(g, -s) for g, s in reversed(y)]
    return xi + yi + x + y

a, ai, b, bi = ('a', 1), ('a', -1), ('b', 1), ('b', -1)
X = [a, bi]
Y1 = [ai, b, a]
Y2 = [ai, ai, b, a, a]
R1 = comm(X, Y1)
R2 = comm(X, Y2)

def evalw(w, P):
    pts = np.arange(len(P[('a', 1)]))
    for t in w:
        pts = P[t][pts]
    return pts

def defects(A, B):
    P = {('a', 1): A, ('a', -1): inv(A), ('b', 1): B, ('b', -1): inv(B)}
    n = len(A); idx = np.arange(n)
    d1 = np.mean(evalw(R1, P) != idx)
    d2 = np.mean(evalw(R2, P) != idx)
    c = np.mean(A[B] != B[A])
    return d1, d2, c

def run(n, eps, iters, seed, lam=4.0):
    rng = np.random.default_rng(seed)
    A = rng.permutation(n); B = rng.permutation(n)
    d1, d2, c = defects(A, B)
    E = d1 + d2 + lam * max(0.0, eps - c)
    best = (E, d1, d2, c)
    T0 = 0.05
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-4
        which = rng.integers(2)
        i, j = rng.integers(n, size=2)
        M = A if which == 0 else B
        M[i], M[j] = M[j], M[i]
        nd1, nd2, nc = defects(A, B)
        nE = nd1 + nd2 + lam * max(0.0, eps - nc)
        if nE <= E or rng.random() < np.exp((E - nE) / T):
            E, d1, d2, c = nE, nd1, nd2, nc
            if nc >= eps and nd1 + nd2 < best[1] + best[2] or (best[3] < eps and nc >= eps):
                best = (E, nd1, nd2, nc)
        else:
            M[i], M[j] = M[j], M[i]
    return {"n": n, "eps": eps, "iters": iters, "seed": seed,
            "best_relator_defect": float(best[1] + best[2]), "best_d1": float(best[1]),
            "best_d2": float(best[2]), "best_commutator": float(best[3])}

if __name__ == "__main__":
    n = int(sys.argv[1]); eps = float(sys.argv[2]); iters = int(sys.argv[3]); seed = int(sys.argv[4])
    print(json.dumps(run(n, eps, iters, seed)), flush=True)
