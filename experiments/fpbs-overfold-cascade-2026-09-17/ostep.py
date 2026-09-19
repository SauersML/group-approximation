"""One-step yield test: can adding ONE seed raise ell by 2 or more?

For k clustered overfold seeds, compute ell for every (k-1)-subset and for the
whole set.  The whole set's ell is an upper bound (candidates inside N), and
it is exact when it is <= 1 (a single lawful seed covering N can be taken
inside N, since on tree-like levels its closure is one pair tree).  We report
jumps ell(P) - max over (k-1)-subsets of ell, and flag jumps >= 2 whose
subset values are exact (all subsets have ell <= 1).
(O-step) = "every jump is <= 1" would give (O-rel) by induction on |P|.

Usage: python3 ostep.py MODEL n k radius trials seed
"""
import itertools
import random
import sys
from oloc import load, Lvl, closure, lawful_part, min_lawful


def ell(L, P, kmax):
    cl = closure(L, P)
    return min_lawful(L, lawful_part(L, cl), kmax)


def main():
    path, n, k, r, trials, seed = sys.argv[1:7]
    n, k, r, trials = int(n), int(k), int(r), int(trials)
    rng = random.Random(int(seed))
    L = Lvl(load(path), n, rng)
    over = [t for t in L.types if not t[2]]
    hist = {}
    ex = None
    for _ in range(trials):
        B = L.ball(rng.randrange(n), r)
        P = []
        for _ in range(k):
            q = rng.choice(B)
            c, d = rng.choice(over)[:2]
            P.append((q * L.Vc + c, q * L.Vc + d))
        full = ell(L, P, k + 1)
        subs = [ell(L, list(S), k) for S in itertools.combinations(P, k - 1)]
        jump = full - max(subs)
        hist[jump] = hist.get(jump, 0) + 1
        if jump >= 2 and ex is None:
            ex = (full, subs, P)
    print('# model', path, 'n', n, 'k', k, 'radius', r, 'trials', trials)
    print('hist jump = ell(P) - max ell(P - s):', sorted(hist.items()))
    print('first jump >= 2 (full, subsets, P):', ex)


if __name__ == '__main__':
    main()
