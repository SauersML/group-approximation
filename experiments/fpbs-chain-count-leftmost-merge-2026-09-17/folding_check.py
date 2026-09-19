# Random test of Lemma 2.1 (folding) of
# research/artifacts/fpbs-chain-count-leftmost-merge-2026-09-19.md:
# for any chain of pairwise distinct hulls X_0..X_n (n >= 2) with X_0 ∩ X_n ≠ ∅,
# some interior hull path p_i has length <= 4.
# Hull of class Ky is y^{-1} T_K. Words over a, A=a^-1, b, B=b^-1.
import random, sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
# core: 0 -a-> 0, 0 -b-> 1, 1 -a-> 2, 1 -b-> 2
FWD = {(0, 'a'): 0, (0, 'b'): 1, (1, 'a'): 2, (1, 'b'): 2}
STEP = dict(FWD)
for (u, s), v in FWD.items():
    STEP[(v, INV[s])] = u


def red(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def mul(*ws):
    return red(''.join(ws))


def read(w):
    """Longest prefix of reduced w readable from core vertex 0; returns (len, end type)."""
    t = 0
    for i, c in enumerate(w):
        if (t, c) not in STEP:
            return i, t
        t = STEP[(t, c)]
    return len(w), t


def proj(h, v):
    """Nearest-point projection of vertex v onto hull h T_K."""
    u = mul(inv(h), v)
    L, _ = read(u)
    return mul(h, u[:L])


def inhull(h, v):
    u = mul(inv(h), v)
    return read(u)[0] == len(u)


def dist(u, v):
    return len(mul(inv(u), v))


def connector(h1, h2):
    """(out in hull h1 T_K, in in hull h2 T_K)."""
    a = proj(h1, h2)
    c = proj(h2, a)
    if inhull(h1, c):
        return c, c
    return proj(h1, c), c


def same_class(y, z):
    w = mul(z, inv(y))
    L, t = read(w)
    return L == len(w) and t == 0


def rand_word(n):
    w = ''
    while len(w) < n:
        w = red(w + random.choice('aAbB'))
    return w


def test(trials, n, maxlen):
    bad = 0
    for _ in range(trials):
        # endpoints K and Kb (both hulls contain core vertex 1); only two
        # classes K b, K ba have hulls through vertex 1 or 2 of T_K, so fix Kb.
        last = 'b'
        ys = ['']
        while len(ys) < n:
            y = rand_word(random.randint(1, maxlen))
            if all(not same_class(y, z) for z in ys + [last]):
                ys.append(y)
        ys.append(last)
        hulls = [inv(y) for y in ys]
        con = [connector(hulls[i - 1], hulls[i]) for i in range(1, n + 1)]
        plen = [dist(con[i - 1][1], con[i][0]) for i in range(1, n)]
        if min(plen) > 4:
            bad += 1
            print('COUNTEREXAMPLE', ys, plen)
    return bad


if __name__ == '__main__':
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    for n in (2, 3, 4, 6, 10):
        for maxlen in (3, 6, 12):
            b = test(500, n, maxlen)
            print('n', n, 'maxlen', maxlen, 'trials 500 violations', b, flush=True)
