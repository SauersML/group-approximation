"""Porteous class of the rank<=1 locus for one-shift certificates of a Rordam root.

Ring: H^*((S^2)^k) = Z[x_1..x_k]/(x_i^2), elements are dicts {bitmask: coeff}.
Root line bundle zeta_J with c1 = x_J = sum_{i in J} x_i; targets zeta_K for r
pairwise disjoint sets K of size m, disjoint from J.  E' = zeta_J^* (x) (+)_K zeta_K,
c(E') = prod_K (1 + x_K - x_J).  Thom-Porteous: the locus {rank <= 1} of a section of
Hom(C^N, E') has class det[c_{r-1+j-i}(E')]_{i,j<=N-1}.  The script reports whether the
class is nonzero, next to the dimension test (N-1)(r-1) <= k = m(r+1).
Usage: python3 porteous_class.py   (runs the grid m<=2, r<=4, N<=4)
"""
import itertools, sys

def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            if ma & mb:
                continue
            m = ma | mb
            out[m] = out.get(m, 0) + ca * cb
    return {m: c for m, c in out.items() if c}

def add(a, b, s=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + s * c
    return {m: c for m, c in out.items() if c}

def linear(idx, sign=1):
    return {1 << i: sign for i in idx}

def chern_classes(m, r):
    J = range(m)
    Ks = [range(m * (t + 1), m * (t + 2)) for t in range(r)]
    total = [{0: 1}]  # graded pieces c_0.. c_r
    for K in Ks:
        y = add(linear(K), linear(J), -1)
        new = [dict() for _ in range(len(total) + 1)]
        for d, c in enumerate(total):
            new[d] = add(new[d], c)
            new[d + 1] = add(new[d + 1], mul(c, y))
        total = new
    return total

def det(M):
    n = len(M)
    if n == 0:
        return {0: 1}
    res = {}
    for perm in itertools.permutations(range(n)):
        sgn = 1
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    sgn = -sgn
        term = {0: sgn}
        for i in range(n):
            term = mul(term, M[i][perm[i]])
            if not term:
                break
        res = add(res, term)
    return res

def porteous(m, r, N):
    c = chern_classes(m, r)
    def cc(d):
        return c[d] if 0 <= d < len(c) else {}
    M = [[cc(r - 1 + j - i) for j in range(N - 1)] for i in range(N - 1)]
    return det(M)

if __name__ == "__main__":
    print("m r N  deg  k  class_nonzero  dim_test (N-1)(r-1)<=m(r+1)  obstruction_on_J_slice (N-1)<=m or (N-1)(r-1)<=rm")
    for m in (1, 2):
        for r in range(1, 5):
            for N in range(2, 5):
                k = m * (r + 1)
                if k > 15:
                    continue
                cls = porteous(m, r, N)
                deg = (N - 1) * (r - 1)
                print(m, r, N, deg, k, bool(cls), deg <= k, deg <= r * m)
                sys.stdout.flush()
