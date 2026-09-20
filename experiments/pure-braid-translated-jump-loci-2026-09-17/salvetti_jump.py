#!/usr/bin/env python3
"""Rank-one local system cohomology of the pure braid group P_n, via the
De Concini--Salvetti complex of the braid group B_n and Shapiro's lemma.

H_*(P_n; L_t) = H_*(B_n; Ind_{P_n}^{B_n} L_t).  Ind L_t is realised as the
monomial representation on basis e_w (w a labelling of the n strand positions):
    sigma_i . e_w = f(w,i) e_{w s_i},  f = t_{ab} if a = w(i) > b = w(i+1), else 1,
where w s_i swaps positions i, i+1.  (The braid relations are palindromic, so this
defines a representation; it is monomial with transitive permutation part, hence
induced from the character of P_n on the line e_id.)

Salvetti complex of an Artin group of finite type with generating set S:
    C_k = free module on subsets Gamma of S with |Gamma| = k,
    d e_Gamma = sum_{sigma in Gamma} sum_{beta in W_Gamma^{Gamma - sigma}}
                (-1)^{l(beta) + mu(Gamma, sigma)} beta~ . e_{Gamma - sigma},
with W_Gamma^{Gamma'} the minimal left coset representatives, beta~ the positive
lift, mu(Gamma, sigma) = #{tau in Gamma : tau < sigma}.
All arithmetic is over the prime field F_P (P large, P = 1 mod 840 so that the
roots of unity of order dividing 840 exist); `generic' means random in F_P^*.
Self-tests: d^2 = 0; Betti numbers of P_n at t = 1.
"""
import itertools, random, sys, json
import numpy as np

P = 2147483647  # placeholder, reset below
def find_prime(mod=840, start=2**26):
    k = start // mod
    while True:
        p = k * mod + 1
        if p > 2 and all(p % q for q in range(2, int(p**0.5) + 1)):
            return p
        k += 1

P = find_prime()

def rank_mod(A, p=None):
    p = p or P
    A = np.array(A, dtype=np.int64) % p
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        if r == rows:
            break
        piv = None
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        col = A[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - np.outer(col[nzr], A[r])) % p
        r += 1
    return r

class Setup:
    def __init__(self, n):
        self.n = n
        self.perms = list(itertools.permutations(range(n)))
        self.idx = {w: i for i, w in enumerate(self.perms)}
        self.N = len(self.perms)
        self.gens = list(range(n - 1))
        # coset representatives with reduced words, per (Gamma, sigma)
        self.cosets = {}
        for k in range(1, n):
            for G in itertools.combinations(self.gens, k):
                elems = self.parabolic(G)
                for s in G:
                    Gp = tuple(x for x in G if x != s)
                    reps = [(w, word) for (w, word) in elems
                            if all(w[i] < w[i + 1] for i in Gp)]
                    mu = sum(1 for x in G if x < s)
                    self.cosets[(G, s)] = (Gp, mu, reps)

    def parabolic(self, G):
        start = tuple(range(self.n))
        seen = {start: ()}
        frontier = [start]
        while frontier:
            nf = []
            for w in frontier:
                for i in G:
                    v = list(w); v[i], v[i + 1] = v[i + 1], v[i]; v = tuple(v)
                    if v not in seen:
                        seen[v] = seen[w] + (i,)
                        nf.append(v)
            frontier = nf
        return list(seen.items())

    def gen_matrices(self, t):
        """t: dict (a,b) a<b -> value in F_P^*.  Returns list of (N x N) matrices."""
        mats = []
        for i in self.gens:
            M = np.zeros((self.N, self.N), dtype=np.int64)
            for w in self.perms:
                a, b = w[i], w[i + 1]
                f = t[(b, a)] if a > b else 1
                v = list(w); v[i], v[i + 1] = v[i + 1], v[i]
                M[self.idx[tuple(v)], self.idx[w]] = f % P
            mats.append(M)
        return mats

    def boundary_mats(self, t):
        g = self.gen_matrices(t)
        N = self.N
        cache = {(): np.eye(N, dtype=np.int64)}
        def lift(word):
            if word in cache:
                return cache[word]
            M = (lift(word[:-1]) @ g[word[-1]]) % P
            cache[word] = M
            return M
        D = {}
        for k in range(1, self.n):
            src = list(itertools.combinations(self.gens, k))
            tgt = list(itertools.combinations(self.gens, k - 1))
            ti = {G: j for j, G in enumerate(tgt)}
            # cochain differential delta: C^{k-1} -> C^k, block (Gamma, Gamma')
            Dk = np.zeros((len(src) * N, len(tgt) * N), dtype=np.int64)
            for j, G in enumerate(src):
                for s in G:
                    Gp, mu, reps = self.cosets[(G, s)]
                    blk = np.zeros((N, N), dtype=np.int64)
                    for (w, word) in reps:
                        sign = (-1) ** (len(word) + mu)
                        blk = (blk + sign * lift(word)) % P
                    r = ti[Gp]
                    Dk[j * N:(j + 1) * N, r * N:(r + 1) * N] = \
                        (Dk[j * N:(j + 1) * N, r * N:(r + 1) * N] + blk) % P
            D[k] = Dk
        return D

    def homology(self, t, check=False):
        D = self.boundary_mats(t)
        n = self.n
        if check:
            for k in range(2, n):
                Z = (D[k] @ D[k - 1]) % P
                assert not Z.any(), f"d^2 != 0 at k={k}"
        ranks = {k: rank_mod(D[k]) for k in D}
        dims = {}
        for k in range(0, n):
            ck = self.N * len(list(itertools.combinations(self.gens, k)))
            rk_out = ranks.get(k, 0)
            rk_in = ranks.get(k + 1, 0)
            dims[k] = ck - rk_out - rk_in
        return [dims[k] for k in range(n)]

def pairs(n):
    return [(a, b) for a in range(n) for b in range(a + 1, n)]

def root_of_unity(order):
    # element of exact multiplicative order `order` in F_P^*
    assert (P - 1) % order == 0
    while True:
        g = random.randrange(2, P - 1)
        z = pow(g, (P - 1) // order, P)
        if all(pow(z, order // q, P) != 1 for q in range(2, order + 1)
               if order % q == 0 and all(q % r for r in range(2, q))):
            return z

def generic_on(n, fixed, zero_sum=True):
    """Random t with t_A := prod_{pairs in A} t = value for each (A, value) in
    fixed (solved by adjusting one pair per constraint), and prod of all t = 1."""
    t = {pq: random.randrange(2, P - 1) for pq in pairs(n)}
    cons = list(fixed)
    if zero_sum:
        cons.append((tuple(range(n)), 1))
    used = set()
    # solve sequentially: pick a free pair in A not used by earlier constraints
    # (constraints are processed smallest first so nested sets work)
    cons.sort(key=lambda c: len(c[0]))
    for A, val in cons:
        cand = [pq for pq in itertools.combinations(sorted(A), 2) if pq not in used]
        free = cand[-1]
        used.update(itertools.combinations(sorted(A), 2))
        prod = 1
        for pq in itertools.combinations(sorted(A), 2):
            if pq != free:
                prod = prod * t[pq] % P
        t[free] = val * pow(prod, P - 2, P) % P
    for A, val in cons:
        prod = 1
        for pq in itertools.combinations(sorted(A), 2):
            prod = prod * t[pq] % P
        assert prod == val % P, (A, val)
    return t

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    random.seed(1)
    S = Setup(n)
    one = {pq: 1 for pq in pairs(n)}
    print("P =", P)
    print("t=1 Betti:", S.homology(one, check=True))
