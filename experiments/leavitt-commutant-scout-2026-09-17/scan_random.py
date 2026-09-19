"""Random scan: for random A in a small box, compute the exact commutant of A in a
larger box and flag commuting B with quadratic joint growth (candidate
algebraically independent pair)."""
import random, sys
from l2 import El, words, ONE, ZERO
from commutant import commutant, growth, randz, box_basis

def rand_el(N, L, density, rng):
    outs = [w for l in range(L + 1) for w in words(l)]
    T = {}
    for m in words(N):
        T[m] = frozenset(w for w in outs if rng.random() < density)
    return El(N, T).reduce()

def main(trials=200, seed=1, NA=1, LA=3, NB=2, LB=5, k=6, dens=0.2):
    rng = random.Random(seed)
    zs = [randz(400, 1000 + i) for i in range(3)]
    flagged = []
    stats = {}
    for tr in range(trials):
        A = rand_el(NA, LA, dens, rng)
        gA = growth(A, ONE, k, zs)
        if gA < k:
            continue  # A algebraic on these vectors
        C = commutant(A, NB, LB)
        best = 0
        for B in C:
            g = growth(A, B, k, zs)
            best = max(best, g)
        # also random combinations
        for _ in range(10):
            B = ZERO
            for c in C:
                if rng.random() < 0.5:
                    B = B + c
            best = max(best, growth(A, B, k, zs))
        stats[best] = stats.get(best, 0) + 1
        if best > 2 * k:
            flagged.append((A, best))
            print('FLAG', best, A, flush=True)
    print('stats (max joint growth at k=%d -> count):' % k, sorted(stats.items()))
    return flagged

if __name__ == '__main__':
    args = [int(a) if a.isdigit() else float(a) for a in sys.argv[1:]]
    main(*args)
