"""Heuristic E_2 membership test for M in SL_2(Z[t, t^-1]) (full-matrix search).

A Laurent polynomial is a pair (low, coeffs) with coeffs[0] != 0 != coeffs[-1].
M = (a, b, c, d).  Moves: R1 <- R1 - m t^k R2, R2 <- R2 - m t^k R1,
C1 <- C1 - m t^k C2, C2 <- C2 - m t^k C1, with integer m and shift k chosen by
aligning one end coefficient of a target entry with one end coefficient of the
source entry (quotient m and m+1).  Success: some entry is +-t^k (then M is in
E_2, since a matrix with a unit entry is elementary up to diag(u, u^-1), and
diagonal matrices of units lie in E_2 by Whitehead's lemma).

States are canonicalized modulo left/right multiplication by diag(t^k, t^-k)
(entry shifts a: k+j, b: k-j, c: j-k, d: -k-j) and global sign.
Failure within the budget is evidence only, never a proof.
"""
import heapq

ZERO = (0, ())


def mk(coeffs, low=0):
    coeffs = list(coeffs)
    while coeffs and coeffs[-1] == 0:
        coeffs.pop()
    i = 0
    while i < len(coeffs) and coeffs[i] == 0:
        i += 1
    if i == len(coeffs):
        return ZERO
    return (low + i, tuple(coeffs[i:]))


def sub_shift(x, y, m, k):
    """x - m t^k y."""
    if not y[1] or m == 0:
        return x
    if not x[1]:
        return mk([-m * v for v in y[1]], y[0] + k)
    ylow = y[0] + k
    low = min(x[0], ylow)
    high = max(x[0] + len(x[1]), ylow + len(y[1]))
    out = [0] * (high - low)
    for i, v in enumerate(x[1]):
        out[x[0] - low + i] += v
    for i, v in enumerate(y[1]):
        out[ylow - low + i] -= m * v
    return mk(out, low)


def mul(x, y):
    if not x[1] or not y[1]:
        return ZERO
    out = [0] * (len(x[1]) + len(y[1]) - 1)
    for i, u in enumerate(x[1]):
        for j, v in enumerate(y[1]):
            out[i + j] += u * v
    return mk(out, x[0] + y[0])


def add(x, y):
    return sub_shift(x, y, -1, 0)


def width(x):
    return len(x[1]) - 1 if x[1] else -1


def l1(x):
    return sum(abs(v) for v in x[1])


def is_unit(x):
    return len(x[1]) == 1 and abs(x[1][0]) == 1


def shift(x, s):
    return (x[0] + s, x[1]) if x[1] else ZERO


def neg(x):
    return (x[0], tuple(-v for v in x[1])) if x[1] else ZERO


def det(M):
    a, b, c, d = M
    return sub_shift(mul(a, d), mul(b, c), 1, 0)


def canon(M):
    a, b, c, d = M
    # shift a and b to low degree 0 when both nonzero: k + j = -a0, k - j = -b0
    # requires a0 + b0 even; otherwise use the parity class representative.
    if a[1] and b[1]:
        s, t_ = -a[0], -b[0]
        if (s + t_) % 2:
            t_ -= 1
        k, j = (s + t_) // 2, (s - t_) // 2
    elif a[1]:
        k, j = -a[0], 0
    else:
        k, j = -b[0], 0
    M = (shift(a, k + j), shift(b, k - j), shift(c, j - k), shift(d, -k - j))
    # sign normalization
    first = next(e for e in M if e[1])
    if first[1][0] < 0:
        M = tuple(neg(e) for e in M)
    return M


def key(M):
    return (sum(max(width(e), 0) for e in M), sum(l1(e) for e in M))


def end_ms(x, y):
    """candidate (m, k) with m t^k y cancelling an end coefficient of x."""
    out = set()
    if not x[1] or not y[1]:
        return out
    xl, xh = x[1][0], x[1][-1]
    yl, yh = y[1][0], y[1][-1]
    # bottom-bottom, top-top, plus bottom of x vs top of y and vice versa
    pairs = [
        (xl, yl, x[0] - y[0]),
        (xh, yh, (x[0] + width(x)) - (y[0] + width(y))),
        (xl, yh, x[0] - (y[0] + width(y))),
        (xh, yl, (x[0] + width(x)) - y[0]),
    ]
    for u, v, k in pairs:
        q = u // v
        for m in (q, q + 1, 1, -1):
            if m:
                out.add((m, k))
    return out


def moves(M):
    a, b, c, d = M
    # row ops: R1 -= m t^k R2 (a -= m t^k c, b -= m t^k d)
    for (x1, x2, y1, y2, pos) in ((a, b, c, d, 0), (c, d, a, b, 1)):
        ms = end_ms(x1, y1) | end_ms(x2, y2)
        for m, k in ms:
            n1, n2 = sub_shift(x1, y1, m, k), sub_shift(x2, y2, m, k)
            yield (n1, n2, c, d) if pos == 0 else (a, b, n1, n2)
    # column ops: C1 -= m t^k C2 (a -= m t^k b, c -= m t^k d)
    for (x1, x2, y1, y2, pos) in ((a, c, b, d, 0), (b, d, a, c, 1)):
        ms = end_ms(x1, y1) | end_ms(x2, y2)
        for m, k in ms:
            n1, n2 = sub_shift(x1, y1, m, k), sub_shift(x2, y2, m, k)
            yield (n1, b, n2, d) if pos == 0 else (a, n1, c, n2)


def reduce_matrix(M, budget=20000, slack=(3, 60), want_path=False):
    M = canon(M)
    assert det(M) in ((0, (1,)),), det(M)
    start = M
    seen = {start}
    parent = {start: None}
    k0 = key(start)
    heap = [(k0, start)]
    best = k0
    steps = 0
    while heap and steps < budget:
        k, M = heapq.heappop(heap)
        steps += 1
        best = min(best, k)
        if any(is_unit(e) for e in M):
            if want_path:
                path = []
                while M is not None:
                    path.append(M)
                    M = parent[M]
                return True, steps, best, path[::-1]
            return True, steps, best
        for N in moves(M):
            N = canon(N)
            if N in seen:
                continue
            kn = key(N)
            if kn[0] > k0[0] + slack[0] or kn[1] > 3 * k0[1] + slack[1]:
                continue
            seen.add(N)
            parent[N] = M
            heapq.heappush(heap, (kn, N))
    return False, steps, best


def cohn(p, q):
    """[[1+pq, p^2], [-q^2, 1-pq]]; p, q are Laurent pairs."""
    one = (0, (1,))
    pq = mul(p, q)
    return (add(one, pq), mul(p, p), neg(mul(q, q)), sub_shift(one, pq, 1, 0))


def mat_mul(M, N):
    a, b, c, d = M
    e, f, g, h = N
    return (add(mul(a, e), mul(b, g)), add(mul(a, f), mul(b, h)),
            add(mul(c, e), mul(d, g)), add(mul(c, f), mul(d, h)))


if __name__ == "__main__":
    for p, q in [((2,), (0, 1)), ((2, 2), (0, 1)), ((2, 3), (3, 2)), ((3, 3), (1, -1))]:
        M = cohn(mk(p), mk(q))
        print(p, q, reduce_matrix(M, 5000))
