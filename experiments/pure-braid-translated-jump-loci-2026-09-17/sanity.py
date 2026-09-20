"""Self-tests for salvetti_jump.py: d^2 = 0 at generic t, generic dimensions,
and the convention t_{jk} = value of the character on the generator A_{jk}."""
import random
import numpy as np
from salvetti_jump import Setup, P, pairs, generic_on

random.seed(7)
for n in (3, 4, 5):
    S = Setup(n)
    t = {pq: random.randrange(2, P - 1) for pq in pairs(n)}
    print(n, "generic (d^2 checked):", S.homology(t, check=True))
    tz = generic_on(n, [])
    print(n, "generic zero-sum:", S.homology(tz, check=True))

def minv(M):
    R = np.zeros_like(M)
    for c in range(M.shape[1]):
        r = np.nonzero(M[:, c])[0][0]
        R[c, r] = pow(int(M[r, c]), P - 2, P)
    return R

n = 4
S = Setup(n)
t = {pq: random.randrange(2, P - 1) for pq in pairs(n)}
g = S.gen_matrices(t)
e = S.idx[tuple(range(n))]
for j in range(n):
    for k in range(j + 1, n):
        word = list(range(k - 1, j, -1))
        M = np.eye(S.N, dtype=np.int64)
        for i in word:
            M = M @ g[i] % P
        M = M @ g[j] % P @ g[j] % P
        for i in reversed(word):
            M = M @ minv(g[i]) % P
        val = M[e, e]
        print("A", (j, k), "acts on e_id by t", [pq for pq in pairs(n) if t[pq] == val],
              "monomial:", np.count_nonzero(M[:, e]) == 1)
