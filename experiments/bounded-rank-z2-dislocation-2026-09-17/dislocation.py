"""Dislocation dipole: permutations A, B of the n x n torus with rank(AB - BA) <= 3
that are at rank distance >= (L-1)M / (2(L+M)) from every commuting pair of matrices.

A = horizontal shift. B = vertical shift, except at the row transition -1 -> 0, where
columns x1..x2 are cyclically shifted: (x,-1) -> (x+1,0) for x1 <= x < x2, (x2,-1) -> (x1,0).

Checks, for each n:
  1. A, B are permutations; AB and BA differ at exactly 3 points, so rank(AB - BA) <= 3
     (exact rank computed over Q).
  2. For w = a^L b^M a^-L b^-M (length 2(L+M)), the permutation w(A,B) moves >= (L-1)M points,
     so rank(w(A,B) - I) = d - #cycles >= moved/2.
  3. Telescoping: if A', B' commute and rank(A-A'), rank(B-B') <= C then w(A',B') = I and
     rank(w(A,B) - I) <= 2(L+M) C. Hence C >= rank(w(A,B)-I) / (2(L+M)).
  4. Upper bound: undoing the interval twist changes B on x2-x1+1 points and gives an exact
     commuting pair, so the distance is Theta(n) = Theta(sqrt d).
Run: nice -n 10 timeout 1200 python3 dislocation.py
"""
from fractions import Fraction


def build(n):
    x1, x2 = n // 4, (3 * n) // 4
    idx = lambda x, y: (y % n) * n + (x % n)
    d = n * n
    A = [0] * d
    B = [0] * d
    for y in range(n):
        for x in range(n):
            A[idx(x, y)] = idx(x + 1, y)
            if y == n - 1 and x1 <= x < x2:  # row -1 = n-1
                B[idx(x, y)] = idx(x + 1, 0)
            elif y == n - 1 and x == x2:
                B[idx(x, y)] = idx(x1, 0)
            else:
                B[idx(x, y)] = idx(x, y + 1)
    return A, B, x1, x2


def inv(P):
    Q = [0] * len(P)
    for i, j in enumerate(P):
        Q[j] = i
    return Q


def compose(P, Q):  # (P o Q)(i) = P(Q(i))
    return [P[Q[i]] for i in range(len(P))]


def power(P, k):
    R = list(range(len(P)))
    for _ in range(k):
        R = compose(P, R)
    return R


def cycles(P):
    seen = [False] * len(P)
    c = 0
    for i in range(len(P)):
        if not seen[i]:
            c += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = P[j]
    return c


def rank_Q(rows):
    rows = [[Fraction(v) for v in r] for r in rows if any(r)]
    rank, col = 0, 0
    ncol = len(rows[0]) if rows else 0
    while rows and col < ncol:
        piv = next((i for i in range(rank, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i][col] != 0:
                f = rows[i][col] / rows[rank][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rank])]
        rank += 1
        col += 1
    return rank


def comm_rank(A, B):
    AB, BA = compose(A, B), compose(B, A)
    bad = [i for i in range(len(A)) if AB[i] != BA[i]]
    # AB - BA is supported on columns in `bad`; exact rank of that d x |bad| block
    d = len(A)
    cols = [[0] * len(bad) for _ in range(d)]
    for j, i in enumerate(bad):
        cols[AB[i]][j] += 1
        cols[BA[i]][j] -= 1
    return len(bad), rank_Q(cols)


def main():
    print("n d  #pts(AB!=BA) rank(AB-BA)  L M  moved(w)  rank(w-I)  C_lower  C_upper")
    for n in [8, 12, 16, 24, 32, 48, 64]:
        A, B, x1, x2 = build(n)
        assert sorted(A) == list(range(n * n)) and sorted(B) == list(range(n * n))
        npts, r = comm_rank(A, B)
        L = M = n // 4
        Ai, Bi = inv(A), inv(B)
        w = compose(power(Bi, M), compose(power(Ai, L), compose(power(B, M), power(A, L))))
        # w applied right-to-left is a^L then b^M then a^-L then b^-M on points
        moved = sum(1 for i in range(n * n) if w[i] != i)
        rk = n * n - cycles(w)
        c_low = Fraction(rk, 2 * (L + M))
        c_up = x2 - x1 + 1
        assert moved >= (L - 1) * M, (n, moved)
        print(n, n * n, npts, r, L, M, moved, rk, float(c_low), c_up)


if __name__ == "__main__":
    main()
