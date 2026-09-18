"""Calibration for rips-segev-one-copy-configurations-carry-no-zero-divisors.

Part 1 (the key lemma, exact, on Steenbock's rows).  Row r has positions
In_r = {0, I1, I2, C} and Out_r = {0, O1, O2, C} with
(I1, I2, O1, O2, C) = 10^(5r-4..5r).  For rows r < r' and all nonempty
supports P_i in In_r, Q_i in Out_r, P_j in In_r', Q_j in Out_r', check:
  (a) every sum x + y (x in row r positions, y in row r' positions) decomposes
      uniquely, so supp(P_i Q_j) = supp P_i + supp Q_j with no cancellation;
  (b) supp P_i + supp Q_j == supp P_j + supp Q_i  implies  all four supports
      lie in {0, C}.
Part 2 (finite linear algebra: the one-copy port system).  A scaled model of
Steenbock's gluing: n lines, fixed-point-free permutations s1..s4, row r with
positions (0, M, 2M, 3M, 4M, 5M) * M_r (so In = {0,M,2M,5M}, Out = {0,3M,4M,5M}).
For fixed u, w in F_p[t] the unknowns are the coefficients of f_i (window
[-D, C_i + D]); the equations say supp(f_i u) in In_i, supp(f_i w) in Out_i,
and (f_l w)(m) + (f_i u)(p) = 0 along every b-edge v_{l,m} -> v_{i,p}.  The
nullspace dimension is computed over F_p.
  * separated rows M_r = 6^(r-1) (min Dist_j > C_i for i < j): theorem says 0;
  * control, degenerate rows M_r = 1 for all r (row separation fails): the pair
    u = P, w = Q built from the port table has the solution f_i = 1 for all i.
Usage: python3 one_copy_ports.py [seed]
"""
import itertools, random, sys
import numpy as np

# ---------------- Part 1 ----------------
def row(r):
    I1, I2, O1, O2, C = (10 ** e for e in range(5 * r - 4, 5 * r + 1))
    return [0, I1, I2, C], [0, O1, O2, C], [0, I1, I2, O1, O2, C]

def nonempty_subsets(xs):
    for k in range(1, len(xs) + 1):
        for c in itertools.combinations(xs, k):
            yield frozenset(c)

def sumset(A, B):
    return frozenset(a + b for a in A for b in B)

def part1(rows):
    checked = 0
    for r, r2 in itertools.combinations(rows, 2):
        In1, Out1, D1 = row(r); In2, Out2, D2 = row(r2)
        sums = {}
        for x in D1:
            for y in D2:
                assert x + y not in sums, "non-unique decomposition"
                sums[x + y] = (x, y)
        C1, C2 = In1[-1], In2[-1]
        S_In1 = list(nonempty_subsets(In1)); S_Out1 = list(nonempty_subsets(Out1))
        S_In2 = list(nonempty_subsets(In2)); S_Out2 = list(nonempty_subsets(Out2))
        left = {}
        for Pi in S_In1:
            for Qj in S_Out2:
                left.setdefault(sumset(Pi, Qj), []).append((Pi, Qj))
        for Pj in S_In2:
            for Qi in S_Out1:
                key = sumset(Pj, Qi)
                checked += 1
                for Pi, Qj in left.get(key, []):
                    assert Pi <= {0, C1} and Qi <= {0, C1} and Pj <= {0, C2} and Qj <= {0, C2}, (r, r2)
    return checked

# ---------------- Part 2 ----------------
P = 10007

def rank_mod_p(A):
    A = A.copy() % P
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i; break
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy(); col[r] = 0
        nz = np.nonzero(col)[0]
        if len(nz):
            A[nz] = (A[nz] - np.outer(col[nz], A[r])) % P
        r += 1
        if r == m:
            break
    return r

def model(n, rng, degenerate):
    perms = []
    for _ in range(4):
        while True:
            p = list(range(n)); rng.shuffle(p)
            if all(p[i] != i for i in range(n)):
                break
        perms.append(p)
    M = [1 if degenerate else 6 ** i for i in range(n)]
    pos = [[k * M[i] for k in range(6)] for i in range(n)]  # 0,I1,I2,O1,O2,C
    edges = []   # (l, m, i, p): b-edge v_{l,m} -> v_{i,p}
    for l in range(n):
        i = perms[0][l]; edges.append((l, pos[l][0], i, pos[i][1]))   # x1: 0 -> I1
        i = perms[1][l]; edges.append((l, pos[l][5], i, pos[i][2]))   # x2: C -> I2
        i = perms[2][l]; edges.append((l, pos[l][3], i, pos[i][5]))   # x3: O1 -> C
        i = perms[3][l]; edges.append((l, pos[l][4], i, pos[i][0]))   # x4: O2 -> 0
    return pos, edges

def nullity(n, pos, edges, u, w, D):
    # f_i supported on [-D, C_i + D]; products on [-D + min, C_i + D + max]
    du, dw = max(u), max(w)
    off = []; tot = 0
    for i in range(n):
        off.append(tot); tot += pos[i][5] + 2 * D + 1
    rows = []
    def prod_row(i, poly, e):
        # coefficient of t^e in f_i * poly
        v = np.zeros(tot, dtype=np.int64)
        for s, c in poly.items():
            k = e - s   # f_i exponent
            if -D <= k <= pos[i][5] + D:
                v[off[i] + k + D] = (v[off[i] + k + D] + c) % P
        return v
    for i in range(n):
        In = {pos[i][0], pos[i][1], pos[i][2], pos[i][5]}
        Out = {pos[i][0], pos[i][3], pos[i][4], pos[i][5]}
        for e in range(-D - max(du, dw) - 1, pos[i][5] + D + max(du, dw) + 2):
            if e not in In:
                rows.append(prod_row(i, u, e))
            if e not in Out:
                rows.append(prod_row(i, w, e))
    for (l, m, i, p) in edges:
        rows.append((prod_row(l, w, m) + prod_row(i, u, p)) % P)
    A = np.array([r for r in rows if r.any()], dtype=np.int64)
    return tot - rank_mod_p(A), tot

def rand_poly(rng, supp):
    return {s: rng.randrange(1, P) for s in supp}

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    c = part1(range(1, 7))
    print("part 1: rows 1..6, %d support quadruple classes checked; unique decomposition and (b) hold" % c)
    n = 4
    for degenerate in (False, True):
        pos, edges = model(n, rng, degenerate)
        tag = "degenerate rows (control)" if degenerate else "separated rows M_r = 6^(r-1)"
        # structured candidate from the port table: P arbitrary on In, Q forced by the edges
        p0, p1, p2, p3 = (rng.randrange(1, P) for _ in range(4))
        Pc = {0: p0, 1: p1, 2: p2, 5: p3}
        Qc = {0: (-p1) % P, 3: (-p3) % P, 4: (-p0) % P, 5: (-p2) % P}
        tests = [("u=P,w=Q from port table", Pc, Qc),
                 ("u=1,w=1", {0: 1}, {0: 1}),
                 ("u=1+t,w=1-t", {0: 1, 1: 1}, {0: 1, 1: P - 1})]
        for k in range(4):
            S = sorted(rng.sample(range(0, 30), 12))
            Su = S[:rng.randrange(2, 11)]; Sw = [s for s in S if s not in Su] or [S[-1]]
            tests.append(("random 12-point S=%s" % S, rand_poly(rng, Su), rand_poly(rng, Sw)))
        for name, u, w in tests:
            nul, tot = nullity(n, pos, edges, u, w, D=8)
            print("part 2: %-30s %-58s unknowns=%5d nullity=%d" % (tag, name, tot, nul))
