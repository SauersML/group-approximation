"""Search binary growth rules on F_2 = <a,b> for injectivity on finite sets.

A rule is a set P of nonzero patterns (x(ga), x(gA), x(gb), x(gB)) in {0,1}^4
(A = a^-1, B = b^-1).  A site g with x(g) = 1 stays 1; a site with x(g) = 0
becomes 1 iff its neighbour pattern lies in P.  So 0 (= c) is quiescent and
never created, and it is destroyed as soon as P is nonempty.

For each rule we test injectivity of S -> T(S) on all subsets S of the ball of
radius R (a necessary condition only), pruning with R = 1 first.

Usage: python3 f2_binary_search.py RMAX
Prints the rules surviving every radius up to RMAX.
"""
import sys
import numpy as np

INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
GENS = "aAbB"


def mul(w, x):
    return w[:-1] if w and w[-1] == INV[x] else w + x


def ball(r):
    words, frontier = [""], [""]
    for _ in range(r):
        nxt = [mul(w, x) for w in frontier for x in GENS if not (w and w[-1] == INV[x])]
        words += nxt
        frontier = nxt
    return words


def prepare(R):
    dom, img = ball(R), ball(R + 1)
    didx = {w: i for i, w in enumerate(dom)}
    n = len(dom)
    S = np.arange(1 << n, dtype=np.uint64)
    one = np.uint64(1)
    zero = np.zeros_like(S)

    def bit(w):
        return ((S >> np.uint64(didx[w])) & one) if w in didx else zero

    rows = []
    for w in img:
        inS = bit(w)
        code = sum(bit(mul(w, x)) << np.uint64(k) for k, x in enumerate(GENS))
        rows.append((inS.astype(bool), code.astype(np.int64)))
    return rows


def collisions(rows, P):
    table = np.zeros(16, dtype=bool)
    for p in P:
        table[p] = True
    T = None
    for j, (inS, code) in enumerate(rows):
        bitj = (inS | table[code]).astype(np.uint64) << np.uint64(j % 64)
        # images live in at most 2 words of 64 bits for R <= 2
        if T is None:
            T = [np.zeros_like(bitj), np.zeros_like(bitj)]
        T[j // 64] |= bitj
    key = T[0] ^ (T[1] * np.uint64(0x9E3779B97F4A7C15))
    order = np.lexsort((T[1], T[0]))
    a0, a1 = T[0][order], T[1][order]
    return int(np.count_nonzero((a0[1:] == a0[:-1]) & (a1[1:] == a1[:-1])))


def main(rmax):
    pats = list(range(1, 16))
    survivors = [frozenset(p for i, p in enumerate(pats) if m >> i & 1)
                 for m in range(1, 1 << 15)]
    for R in range(1, rmax + 1):
        rows = prepare(R)
        survivors = [P for P in survivors if collisions(rows, P) == 0]
        print(f"R={R}: {len(survivors)} surviving rules", flush=True)
    for P in survivors[:40]:
        print(sorted(format(p, "04b")[::-1] for p in P))


if __name__ == "__main__":
    main(int(sys.argv[1]))
