"""Check the ternary tree-growth automaton of pre-injective-automata-can-destroy-never-created-letters.

G = F_2 = <a,b>, A = a^-1, B = b^-1, memory {1, a, A, b, B}.
Alphabet {c, 0, 1}, stored as c = 2.  Slot maps
    alpha (slots a, b):  c -> 0, 0 -> 0, 1 -> 1
    beta  (slots A, B):  c -> 1, 0 -> 0, 1 -> 0
so letter -> (alpha, beta) is injective.  Local rule at k:
    x(k) = e in Z/2 :  y(k) = e + sum_s phi_s(x(ks))  mod 2
    x(k) = c        :  y(k) = c if all four neighbours are c,
                       else y(k) = sum_s phi_s(x(ks)) mod 2.

Tests (necessary conditions; the proof is in the research node):
 1. growth: one letter in a c background gives exactly 5 non-c sites;
 2. exhaustive: for many backgrounds outside the 1-ball, the 3^5 fillings of
    the 1-ball have pairwise distinct images on the 2-ball;
 3. random asymptotic pairs differing on random finite sets inside the 3-ball,
    over random backgrounds, always have different images.

Usage: python3 verify_preinjective.py SEED
"""
import itertools
import random
import sys

INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
GENS = "aAbB"
C = 2
ALPHA = {C: 0, 0: 0, 1: 1}
BETA = {C: 1, 0: 0, 1: 0}
PHI = {"a": ALPHA, "b": ALPHA, "A": BETA, "B": BETA}


def mul(w, x):
    return w[:-1] if w and w[-1] == INV[x] else w + x


def ball(r):
    words, frontier = [""], [""]
    for _ in range(r):
        nxt = [mul(w, x) for w in frontier for x in GENS if not (w and w[-1] == INV[x])]
        words += nxt
        frontier = nxt
    return words


def out(x, k):
    """y(k); x is a dict word -> letter with default c."""
    nb = [x.get(mul(k, s), C) for s in GENS]
    tot = sum(PHI[s][v] for s, v in zip(GENS, nb)) % 2
    e = x.get(k, C)
    if e != C:
        return (e + tot) % 2
    if all(v == C for v in nb):
        return C
    return tot


def image(x, sites):
    return tuple(out(x, k) for k in sites)


def main(seed):
    rng = random.Random(seed)
    # 1. growth
    for e in (0, 1):
        x = {"": e}
        noncs = [k for k in ball(3) if out(x, k) != C]
        assert len(noncs) == 5, noncs
    print("growth: a single letter gives 5 non-c sites")

    # 2. exhaustive on the 1-ball
    b1, b2, b3 = ball(1), ball(2), ball(3)
    shell = [w for w in b3 if w not in set(b1)]
    trials = 0
    for t in range(300):
        if t == 0:
            bg = {}
        else:
            p = rng.random()
            bg = {w: (C if rng.random() < p else rng.randrange(2)) for w in shell}
        seen = {}
        for fill in itertools.product((0, 1, C), repeat=len(b1)):
            x = dict(bg)
            x.update(zip(b1, fill))
            im = image(x, b2)
            assert im not in seen, (bg, fill, seen[im])
            seen[im] = fill
        trials += 1
    print(f"exhaustive: {trials} backgrounds, 3^5 fillings each, all images distinct")

    # 3. random asymptotic pairs
    b5 = ball(5)
    b4 = ball(4)
    pairs = 0
    for t in range(20000):
        p = rng.random()
        x = {w: (C if rng.random() < p else rng.randrange(2)) for w in b5}
        D = rng.sample(b3, rng.randrange(1, 12))
        x2 = dict(x)
        for w in D:
            x2[w] = rng.choice([v for v in (0, 1, C) if v != x[w]])
        assert image(x, b4) != image(x2, b4), (x, D)
        pairs += 1
    print(f"random: {pairs} asymptotic pairs, all images distinct")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
