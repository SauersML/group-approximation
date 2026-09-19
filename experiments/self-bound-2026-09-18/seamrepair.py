"""Proposition 3 check: the one-cylinder surface with circumference n, height H >= n and seam permutation sigma
(c(i, H-1) = (sigma(i), 0)) is within rank d(sigma) < 4 rho of a torus, where
d(sigma) = min_j rank(rho_j^-1 sigma - I) and rho_j is the rotation i -> i + j.  Exhaustive over all sigma in
Sym(n) for n <= 6 with H = n, and n = 7 with H = 7.  Checks, with the actual surface permutations:
  (1) c^H = sigma on every row;  (2) the repaired c' (top row glued by the best rotation) commutes with b;
  (3) rank(c' c^-1 - I) = d(sigma);  (4) d(sigma) <= n - max_j |C_j| <= max_s m_s <= 2 max_s r_s, where
  m_s, r_s = moved points and rank of [R^s, sigma];  (5) d(sigma) < 4 * H r_s / (s + H) for the best s, a lower
  bound for rho computed on the surface as rank([b^s, c^H] - I) / (s + H)."""
import sys, itertools
from swap import comp, inv, power, rank_minus_I

def surf(n, H, sig):
    d = n*H; b = [0]*d; c = [0]*d
    for r in range(H):
        for i in range(n):
            b[r*n+i] = r*n + (i+1) % n
            c[r*n+i] = (r+1)*n + i if r < H-1 else sig[i]
    return b, c

def comm(f, g): return comp(f, comp(g, comp(inv(f), inv(g))))

def check(n, H):
    worst = 0.0; cnt = 0
    for sig in itertools.permutations(range(n)):
        b, c = surf(n, H, sig); cH = power(c, H)
        assert all(cH[r*n+i] == r*n + sig[i] for r in range(H) for i in range(n))
        R = [(i+1) % n for i in range(n)]
        dj = [rank_minus_I(comp(inv([(i+j) % n for i in range(n)]), list(sig))) for j in range(n)]
        j = min(range(n), key=lambda j: dj[j]); dsig = dj[j]
        c2 = list(c)
        for i in range(n): c2[(H-1)*n+i] = (i+j) % n
        assert comm(b, c2) == list(range(n*H))
        assert rank_minus_I(comp(c2, inv(c))) == dsig
        cls = max(sum(1 for i in range(n) if (sig[i]-i) % n == jj) for jj in range(n))
        ms = []; rs = []; lb = 0.0
        for s in range(1, n):
            k = comm(power(R, s), list(sig)); ms.append(sum(1 for x in range(n) if k[x] != x)); rs.append(rank_minus_I(k))
            lb = max(lb, rank_minus_I(comm(power(b, s), cH)) / (s + H))
        assert dsig <= n - cls <= max(ms + [0]) <= 2*max(rs + [0])
        assert dsig == 0 or dsig < 4*lb
        if dsig: worst = max(worst, dsig/lb)
        cnt += 1
    return cnt, worst

if __name__ == '__main__':
    for n in range(2, 8):
        print(n, check(n, n), flush=True)
