"""Tries random eta for several characters; reports the reduced Betti numbers of
the ascending links Asc(C) over all chambers C (worst case), per trial."""
import sys, random, itertools
from fractions import Fraction
from salvetti_morse import Morse, order_complex_homology, random_eta, pairs

AMP = [1, 5, 20, 60, 150]

def run(n, a, trials, m, seed=1, maxdim=None):
    rng = random.Random(seed)
    best = None
    for tr in range(trials):
        eta = random_eta(n, AMP[tr % len(AMP)], rng)
        if tr == 0:
            # tiny tie-breaks only
            eta = {C: Fraction(rng.randrange(1, 10**6), 10**12) for C in eta}
        M = Morse(n, a, eta)
        bad = 0
        worst = None
        for C in itertools.permutations(range(n)):
            els = M.asc_poset(C)
            b = order_complex_homology(els, maxdim=maxdim if maxdim is not None else m)
            ok = b != [-1] and all(x == 0 for x in b[:m])
            if not ok:
                bad += 1
                worst = (C, len(els), b)
        print(f"  trial {tr}: bad chambers {bad}", worst if worst else "", flush=True)
        if bad == 0:
            return True
    return False

if __name__ == "__main__":
    n = int(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3])
    kind = sys.argv[4]
    rng = random.Random(5)
    P = pairs(n)
    a = {p: Fraction(rng.randrange(-50, 51)) for p in P}
    if kind in ("zerosum", "c01", "c012", "tri"):
        s = sum(a.values()); a[P[-1]] -= s
    if kind == "c01":
        # c_01 = 0, keep zero sum: move a_01 onto a pair disjoint... adjust last pair
        d = a[(0, 1)]; a[(0, 1)] = Fraction(0); a[P[-1]] += d
    if kind == "c012":
        d = a[(0, 1)] + a[(0, 2)] + a[(1, 2)]; a[(1, 2)] -= d; a[P[-1]] += d
    if kind == "tri":
        a = {p: Fraction(0) for p in P}
        a[(0, 1)], a[(0, 2)], a[(1, 2)] = Fraction(3), Fraction(-7), Fraction(4)
    print(kind, {k: str(v) for k, v in a.items()}, "sum", sum(a.values()))
    print("certified" if run(n, a, trials, m) else "no certificate")
