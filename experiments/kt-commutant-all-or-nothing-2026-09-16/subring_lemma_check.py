"""Randomized check of the combinatorial core of the subring dichotomy lemma
(route kt-compressor-commutant-collapse-all-or-nothing-proof, Steps 1-5).

Given a finite set of exponent vectors supp(f_-) in Z^d \\ N^d, the lemma
produces P in A_d, L in SL_d(N), n in N^d, and L' in SL_d(N) such that
x^n * beta_L(beta_P(f_-)) = c x^{m'} + (polynomial) with m'_1 < 0,
m'_k >= 0 for k >= 2, and beta_{L'}(x^{(-1,b)}) = x_1^{-1}.
Coefficients play no role (distinct exponents never cancel), so only
exponent sets are tracked.  beta_L(x^n) = x^{L n}.
"""
import itertools, random, sys

def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    return sum((-1) ** j * M[0][j] * det([row[:j] + row[j+1:] for row in M[1:]]) for j in range(n))

def matvec(M, v):
    return tuple(sum(a * b for a, b in zip(row, v)) for row in M)

def even_perm_to(k, d):
    """An even permutation p of range(d) with p[k] = 0, as a matrix P with P e_k = e_0."""
    for p in itertools.permutations(range(d)):
        inv = sum(1 for i in range(d) for j in range(i + 1, d) if p[i] > p[j])
        if inv % 2 == 0 and p[k] == 0:
            P = [[0] * d for _ in range(d)]
            for i in range(d):
                P[p[i]][i] = 1
            return P
    raise RuntimeError

def run(d, supp):
    assert all(any(c < 0 for c in m) for m in supp)
    # Step 1: move a negative coordinate of some monomial to coordinate 1 (index 0).
    m0 = supp[0]
    k = min(i for i in range(d) if m0[i] < 0)
    P = even_perm_to(k, d)
    assert det(P) == 1 and all(x >= 0 for row in P for x in row)
    supp = [matvec(P, m) for m in supp]
    assert any(m[0] < 0 for m in supp)
    # Step 2: psi = (K^{d-1},...,K,1) with K > 2M.
    M = max(max(abs(c) for c in m) for m in supp)
    K = 2 * M + 1
    psi = [K ** (d - 1 - i) for i in range(d)]
    vals = [sum(a * b for a, b in zip(psi, m)) for m in supp]
    assert len(set(vals)) == len(vals), "psi not injective"
    order_psi = sorted(range(len(supp)), key=lambda j: vals[j])
    order_lex = sorted(range(len(supp)), key=lambda j: supp[j])
    assert order_psi == order_lex, "psi does not order lexicographically"
    j0 = order_psi[0]
    assert supp[j0][0] < 0 and vals[j0] < 0
    # Step 3: L with rows psi, e_1*, ..., e_{d-1}* (swap rows 2,3 if d even).
    rows = [psi] + [[1 if c == i else 0 for c in range(d)] for i in range(d - 1)]
    if d % 2 == 0:
        rows[1], rows[2] = rows[2], rows[1]
    L = rows
    assert det(L) == 1 and all(x >= 0 for row in L for x in row)
    img = [matvec(L, m) for m in supp]
    assert len(set(img)) == len(img)
    # Step 4: multiply by x^n.
    N = M
    others = [vals[j] for j in range(len(supp)) if j != j0]
    n1 = max([0] + [-v for v in others])
    n = (n1,) + (N,) * (d - 1)
    shifted = [tuple(a + b for a, b in zip(v, n)) for v in img]
    for j, v in enumerate(shifted):
        if j != j0:
            assert all(c >= 0 for c in v), (j, v)
    mp = shifted[j0]
    assert mp[0] < 0 and all(c >= 0 for c in mp[1:])
    # Step 5: x_1^{a-1} x^{m'} = x^{(-1,b)}; L' = I + sum_k b_k E_{k1}.
    b = mp[1:]
    v = (-1,) + b
    Lp = [[1 if i == j else 0 for j in range(d)] for i in range(d)]
    for i in range(1, d):
        Lp[i][0] = b[i - 1]
    assert det(Lp) == 1 and all(x >= 0 for row in Lp for x in row)
    assert matvec(Lp, v) == (-1,) + (0,) * (d - 1)
    return True

def main():
    random.seed(20260916)
    trials = 0
    for d in (3, 4, 5):
        for _ in range(3000):
            size = random.randint(1, 6)
            R = random.randint(1, 4)
            supp = set()
            while len(supp) < size:
                m = tuple(random.randint(-R, R) for _ in range(d))
                if any(c < 0 for c in m):
                    supp.add(m)
            run(d, sorted(supp, key=lambda _: random.random()))
            trials += 1
    print("all checks passed:", trials, "random supports, d in {3,4,5}")

if __name__ == "__main__":
    main()
