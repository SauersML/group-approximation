"""Thue-Morse point of Ledrappier's shift and its window sub-SFTs.

y(i, n) = (F^n TM)(i), F = 1 + sigma over F_2, i.e. y(i, n+1) = y(i, n) + y(i+1, n).
Since TM(2i) = TM(i), the upper half of y is fixed by the dilation x -> x(2 .).

A_L = set of length-L row words of y (on a large quadrant).  Omega(A_L) contains the
orbit closure of y.  This script
  1. computes A_L and checks its stability under enlarging the quadrant;
  2. searches for doubly periodic points of Omega(A_L): an F-cycle of m-periodic
     rows all of whose length-L words lie in A_L, for m <= MMAX.
Usage: python3 tm_ledrappier.py L MMAX [N NT]
"""
import sys
import numpy as np


def tm(N):
    x = np.zeros(N, dtype=np.uint8)
    for i in range(1, N):
        x[i] = x[i >> 1] ^ (i & 1)
    return x


def row_words(N, NT, L):
    row = tm(N)
    seen = set()
    for n in range(NT):
        m = len(row)
        codes = np.zeros(m - L + 1, dtype=np.int64)
        for s in range(L):
            codes = codes * 2 + row[s:m - L + 1 + s]
        seen.update(np.unique(codes).tolist())
        row = row[:-1] ^ row[1:]
    return seen


def periodic_rows(A, L, m):
    """All m-periodic binary rows (as tuples of length m) whose cyclic L-words lie in A."""
    mask = (1 << (L - 1)) - 1
    out = []
    # DFS over sequences of length m + L - 1, closing cyclically
    def dfs(seq, code):
        if len(seq) == m:
            # check wrap-around windows
            ext = [seq[j % m] for j in range(m + L - 1)]
            c = 0
            for s in range(L):
                c = c * 2 + ext[s]
            ok = True
            for i in range(m):
                if i > 0:
                    c = ((c << 1) & ((1 << L) - 1)) | ext[i + L - 1]
                if c not in A:
                    ok = False
                    break
            if ok:
                out.append(tuple(seq))
            return
        for b in (0, 1):
            nc = ((code << 1) | b)
            if len(seq) + 1 >= L:
                if (nc & ((1 << L) - 1)) not in A:
                    continue
            dfs(seq + [b], nc & ((1 << L) - 1))
    dfs([], 0)
    return out


def rowset_ok(p, A, L):
    m = len(p)
    ext = [p[j % m] for j in range(m + L - 1)]
    for i in range(m):
        c = 0
        for s in range(L):
            c = c * 2 + ext[i + s]
        if c not in A:
            return False
    return True


def find_cycle(A, L, m):
    rows = periodic_rows(A, L, m)
    good = set(rows)
    status = {}
    for p in rows:
        path = []
        q = p
        while q in good and q not in status and q not in path:
            path.append(q)
            q = tuple(q[i] ^ q[(i + 1) % m] for i in range(m))
        if q in path:  # cycle inside good
            return len(rows), q
        for r in path:
            status[r] = False
    return len(rows), None


if __name__ == "__main__":
    L = int(sys.argv[1]); MMAX = int(sys.argv[2])
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 1 << 15
    NT = int(sys.argv[4]) if len(sys.argv) > 4 else 4096
    A = row_words(N, NT, L)
    A2 = row_words(N // 2, NT // 2, L)
    print(f"L={L} |A_L|={len(A)} of {2**L}; half-size quadrant gives {len(A2)}")
    for m in range(1, MMAX + 1):
        nrows, cyc = find_cycle(A, L, m)
        print(f"  m={m}: rows in Y_A = {nrows}; periodic point: {'YES ' + ''.join(map(str, cyc)) if cyc else 'no'}", flush=True)
        if cyc:
            break
