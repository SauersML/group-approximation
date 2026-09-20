"""Hill-climb over eta to find a Bestvina--Brady certificate on the Salvetti complex.
Score = sum over chambers of the defect of Asc(C) (reduced Betti numbers in degrees
< m, plus 1 if Asc(C) is empty).  A score of 0 certifies [chi] in Sigma^m(P_n; Z)
over F_p (homological, at the prime used); see salvetti_morse.py."""
import sys, random, itertools, json
from fractions import Fraction
from salvetti_morse import Morse, order_complex_homology, random_eta, pairs

def defect(M, C, m):
    els = M.asc_poset(C)
    b = order_complex_homology(els, maxdim=m - 1)
    if b == [-1]:
        return 1 + m, b
    return sum(b[:m]), b

def score(n, a, eta, m, chambers):
    M = Morse(n, a, eta)
    tot, per = 0, {}
    for C in chambers:
        try:
            d, b = defect(M, C, m)
        except ValueError:
            d, b = 99, None
        per[C] = d
        tot += d
    return tot, per

def climb(n, a, m, steps, seed, amp=20, verbose=True):
    rng = random.Random(seed)
    chambers = list(itertools.permutations(range(n)))
    eta = random_eta(n, amp, rng)
    s, per = score(n, a, eta, m, chambers)
    for it in range(steps):
        if s == 0:
            break
        bad = [C for C in chambers if per[C] > 0]
        C0 = rng.choice(bad)
        # perturb eta at C0 or at a neighbour of C0
        C1 = list(C0)
        if rng.random() < 0.5:
            i = rng.randrange(n - 1); C1[i], C1[i + 1] = C1[i + 1], C1[i]
        C1 = tuple(C1)
        new = dict(eta)
        new[C1] = eta[C1] + Fraction(rng.randrange(-amp * 10**6, amp * 10**6 + 1), 10**6)
        s2, per2 = score(n, a, new, m, chambers)
        if s2 <= s:
            eta, s, per = new, s2, per2
        if verbose and it % 20 == 0:
            print(f"   step {it}: score {s}", flush=True)
    return s, eta

if __name__ == "__main__":
    n, m, steps = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    vals = json.loads(sys.argv[4])  # list of a_ij in pairs(n) order
    a = {p: Fraction(v) for p, v in zip(pairs(n), vals)}
    print("a =", vals, "sum", sum(a.values()))
    for seed in range(int(sys.argv[5]) if len(sys.argv) > 5 else 3):
        s, eta = climb(n, a, m, steps, seed)
        print("seed", seed, "final score", s, flush=True)
        if s == 0:
            print("CERTIFIED")
            break
