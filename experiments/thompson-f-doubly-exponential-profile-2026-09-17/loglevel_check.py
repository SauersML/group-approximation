"""Checks for thompson-f-near-eigenvectors-doubly-exponential-proof.

Part A: the eight set inclusions of Step 4 of the route, on every size tuple
         (n_-2, ..., n_4) with entries in [1, B], plus random tuples with large
         entries.  The moves are applied literally to the tuple, so the pull-back
         formulas are tested too.  All comparisons are exact integer arithmetic.
Part B: exhaustive search, for small K, of the smallest possible maximum of a
         window x_-K..x_K that is good at level 0 and at level 1 (Step 7), compared
         with the proved lower bound phi ** F(ceil((K-1)/2)).
Run: python3 loglevel_check.py
"""
import itertools
import math
import random

OFF = 2  # tuple index of n_0; tuple t = (n_-2, n_-1, n_0, n_1, n_2, n_3, n_4)


def n(t, j):
    return t[j + OFF]


def mu(t):
    # merge T_i and T_(i+1): n_0 -> n_0 + n_1, n_j -> n_(j+1) for j >= 1
    # (last slot becomes unknown; events never read it after one move)
    return (t[0], t[1], t[2] + t[3]) + t[4:] + (None,)


def rho(t):
    # pointer right: n_j -> n_(j+1)
    return t[1:] + (None,)


# ---- level 0 -------------------------------------------------------------
def C1(a, b, c):
    return b <= c < a + b


def C2(a, b, c):
    return b <= a < b + c


def bad0(t, j):  # pointer assumed deep enough
    a, b, c = n(t, j - 1), n(t, j), n(t, j + 1)
    return C1(a, b, c) or C2(a, b, c)


# ---- level 1, written multiplicatively ------------------------------------
# increasing: y_j = log(n_(j+1)/n_j); decreasing: z_j = log(n_j/n_(j+1))
def Ainc(t, k):
    return n(t, k - 1) < n(t, k) < n(t, k + 1) < n(t, k + 2)


def Adec(t, k):
    return n(t, k - 1) > n(t, k) > n(t, k + 1) > n(t, k + 2)


def C1inc(t, k):  # y_k <= y_(k+1) < y_(k-1) + y_k
    a, b, c, d = (n(t, k + s) for s in (-1, 0, 1, 2))
    return Ainc(t, k) and c * c <= b * d and a * d < c * c


def C2inc(t, k):  # y_k <= y_(k-1) < y_k + y_(k+1)
    a, b, c, d = (n(t, k + s) for s in (-1, 0, 1, 2))
    return Ainc(t, k) and a * c <= b * b and b * b < a * d


def C1dec(t, k):  # z_k <= z_(k+1) < z_(k-1) + z_k
    a, b, c, d = (n(t, k + s) for s in (-1, 0, 1, 2))
    return Adec(t, k) and b * d <= c * c and c * c < a * d


def C2dec(t, k):  # z_k <= z_(k-1) < z_k + z_(k+1)
    a, b, c, d = (n(t, k + s) for s in (-1, 0, 1, 2))
    return Adec(t, k) and b * b <= a * c and a * d < b * b


# ---- test events -----------------------------------------------------------
def E2inc(t):  # y_-2 < y_-1
    return n(t, -1) ** 2 < n(t, -2) * n(t, 0)


def E1inc(t):  # n_-1 < n_0 and y_-1 > y_0
    return n(t, -1) < n(t, 0) and n(t, 0) ** 2 > n(t, -1) * n(t, 1)


def E1dec(t):  # z_0 > z_1
    return n(t, 0) * n(t, 2) > n(t, 1) ** 2


def E2dec(t):  # n_0 > n_1 and z_-1 < z_0
    return n(t, 0) > n(t, 1) and n(t, -1) * n(t, 1) < n(t, 0) ** 2


def check(t, fails):
    m, r = mu(t), rho(t)
    tests = [
        ("E2inc subset mu^-1 E2inc", (not E2inc(t)) or E2inc(m)),
        ("C2inc_-1 subset mu^-1E2inc - E2inc", (not C2inc(t, -1)) or (E2inc(m) and not E2inc(t))),
        ("C1inc_0 subset mu^-1E1inc - rho^-1E1inc", (not C1inc(t, 0)) or (E1inc(m) and not E1inc(r))),
        ("rho^-1E1inc - mu^-1E1inc subset bad_0", (not (E1inc(r) and not E1inc(m))) or bad0(t, 0)),
        ("rho^-1E1dec subset mu^-1E1dec", (not E1dec(r)) or E1dec(m)),
        ("C1dec_1 subset mu^-1E1dec - rho^-1E1dec", (not C1dec(t, 1)) or (E1dec(m) and not E1dec(r))),
        ("C2dec_0 subset mu^-1E2dec - E2dec", (not C2dec(t, 0)) or (E2dec(m) and not E2dec(t))),
        ("E2dec - mu^-1E2dec subset bad_1", (not (E2dec(t) and not E2dec(m))) or bad0(t, 1)),
        ("rho^-1 C1inc_0 = C1inc_1", C1inc(r, 0) == C1inc(t, 1)),
    ]
    for name, ok in tests:
        if not ok:
            fails[name] = fails.get(name, 0) + 1


def part_a(B=7, samples=300000):
    fails = {}
    count = 0
    for t in itertools.product(range(1, B + 1), repeat=7):
        check(t, fails)
        count += 1
    rnd = random.Random(20260919)
    for _ in range(samples):
        scale = 10 ** rnd.randint(1, 7)
        t = tuple(rnd.randint(1, scale) for _ in range(7))
        check(t, fails)
        count += 1
    print(f"Part A: {count} tuples, failures: {fails if fails else 'none'}")
    print("Part A", "OK" if not fails else "FAIL")


def nonvacuous(B=7):
    # how often each level-1 event occurs among the exhaustive tuples
    names = {"C1inc_0": lambda t: C1inc(t, 0), "C2inc_-1": lambda t: C2inc(t, -1),
             "C1dec_1": lambda t: C1dec(t, 1), "C2dec_0": lambda t: C2dec(t, 0)}
    cnt = {k: 0 for k in names}
    for t in itertools.product(range(1, B + 1), repeat=7):
        for k, fn in names.items():
            cnt[k] += fn(t)
    print("Part A occurrence counts (B=%d):" % B, cnt)


def fib(m):
    a, b = 0, 1
    for _ in range(m):
        a, b = b, a + b
    return a


def good_prefix(x, K):
    """x is a prefix x_-K..x_(-K+len-1); check the constraints completed by its last entry."""
    L = len(x)
    # level-0 at offset whose right neighbour is the last entry (interior offsets only)
    if L >= 3:
        a, b, c = x[L - 3], x[L - 2], x[L - 1]
        if C1(a, b, c) or C2(a, b, c):
            return False
    if L >= 4:
        t = (0,) + tuple(x[L - 4:L]) + (0, 0)  # n_-1..n_2 = last four entries; use k = 0
        if C1inc(t, 0) or C2inc(t, 0) or C1dec(t, 0) or C2dec(t, 0):
            return False
    return True


def exists(K, M):
    W = 2 * K + 1
    stack = [[v] for v in range(1, M + 1)]
    while stack:
        x = stack.pop()
        if len(x) == W:
            return x
        cand = range(1, M + 1)
        if len(x) >= 2:  # speed-up only: level-0 goodness forces one of these (Step 3 local step)
            a, b = x[-2], x[-1]
            cand = list(range(1, b)) + list(range(a + b, M + 1)) if a < b else range(1, b)
        for v in cand:
            y = x + [v]
            if good_prefix(y, K):
                stack.append(y)
    return None


def part_b(Kmax=5):
    phi = (1 + 5 ** 0.5) / 2
    ok = True
    for K in range(2, Kmax + 1):
        M = 1
        while True:
            w = exists(K, M)
            if w is not None:
                break
            M += 1
        bound = phi ** fib(math.ceil((K - 1) / 2))
        good = M >= bound
        ok &= good
        print(f"K={K}: min max = {M} (window {w}); level-0 bound F_(K+2) = {fib(K + 2)}; "
              f"level-1 bound phi^F(ceil((K-1)/2)) = {bound:.3f}; {'OK' if good else 'FAIL'}")
    print("Part B", "OK" if ok else "FAIL")


if __name__ == "__main__":
    part_a()
    nonvacuous(6)
    part_b(4)
