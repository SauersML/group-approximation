#!/usr/bin/env python3
"""Exact checks behind density-random-groups-no-finite-quotients-below-exp-k and
density-random-simple-quotient-first-moment-diverges (lane solve-hyperbolic-rf, 2026-09-13).

All arithmetic is exact (integers and Fractions).

(a) C_L, the number of cyclically reduced words of length L in F_m, equals
    (2m-1)^L + 1 for L odd and (2m-1)^L + 2m - 1 for L even.
(b) Transfer matrix T = J - P satisfies T^n = (-P)^n + ((2m-1)^n - (-1)^n) J / (2m).
(c) Window bound: min over letters x of P(w_1 = x, w_3 = x) >= (m-1)/(2m(2m-1)^2).
(d) For homomorphisms phi: F_m -> Q into small permutation groups that are non-constant on
    the 2m letters, P(phi(w) = 1) <= 1 - kappa_m with kappa_m = (m-1)/(2m(2m-1)^3).
    Constant assignments are the trivial map and the length-parity map.
(e) <(1 2 3), (1 2 ... n)> = A_n for n = 5, 7, 9.
(f) The words x a^3 x^-1 y a^3 y^-1 z a^3 z^-1 (|x|=|y|=|z|=r, with the stated letter
    conditions) are distinct cyclically reduced words of length 6r+9, and their number is
    at least 2m(2m-1)(2m-2)[(2m-1)^(r-2)(2m-3)]^3.
"""
from fractions import Fraction
import itertools, json, random, math

def letters(m):
    return [(i, s) for i in range(m) for s in (1, -1)]

def inv(x):
    return (x[0], -x[1])

def cr_words(m, L):
    A = letters(m)
    out = []
    w = [None] * L
    def rec(k):
        if k == L:
            if w[L - 1] != inv(w[0]):
                out.append(tuple(w))
            return
        for a in A:
            if k > 0 and a == inv(w[k - 1]):
                continue
            w[k] = a
            rec(k + 1)
    rec(0)
    return out

def is_cyclically_reduced(w):
    L = len(w)
    return all(w[(i + 1) % L] != inv(w[i]) for i in range(L))

def C_formula(m, L):
    return (2 * m - 1) ** L + (1 if L % 2 else 2 * m - 1)

def matmul(X, Y):
    n = len(X)
    return [[sum(X[i][k] * Y[k][j] for k in range(n)) for j in range(n)] for i in range(n)]

def check_transfer(m, nmax):
    A = letters(m)
    idx = {a: i for i, a in enumerate(A)}
    N = 2 * m
    T = [[0 if A[j] == inv(A[i]) else 1 for j in range(N)] for i in range(N)]
    P = [[1 if A[j] == inv(A[i]) else 0 for j in range(N)] for i in range(N)]
    I = [[1 if i == j else 0 for j in range(N)] for i in range(N)]
    Tn = I
    ok = True
    for n in range(nmax + 1):
        Pn = I if n % 2 == 0 else P
        sgn = (-1) ** n
        coef = Fraction((2 * m - 1) ** n - sgn, 2 * m)
        for i in range(N):
            for j in range(N):
                pred = sgn * Pn[i][j] + coef
                if Fraction(Tn[i][j]) != pred:
                    ok = False
        Tn = matmul(Tn, T)
    return ok

def perm_mul(p, q):
    # (p*q)(i) = p(q(i))
    return tuple(p[q[i]] for i in range(len(p)))

def perm_inv(p):
    r = [0] * len(p)
    for i, pi in enumerate(p):
        r[pi] = i
    return tuple(r)

def closure(gens):
    n = len(gens[0])
    e = tuple(range(n))
    seen = {e}
    frontier = [e]
    while frontier:
        new = []
        for g in frontier:
            for s in gens:
                h = perm_mul(g, s)
                if h not in seen:
                    seen.add(h)
                    new.append(h)
        frontier = new
    return seen

def word_prob_trivial(words, img):
    e = tuple(range(len(next(iter(img.values())))))
    hits = 0
    for w in words:
        g = e
        for a in w:
            g = perm_mul(g, img[a])
        if g == e:
            hits += 1
    return Fraction(hits, len(words))

def check_kappa(m, L, group_elems, tuples):
    words = cr_words(m, L)
    kappa = Fraction(m - 1, 2 * m * (2 * m - 1) ** 3)
    worst = Fraction(0)
    worst_tuple = None
    violations = 0
    constant_seen = []
    for tup in tuples:
        img = {}
        for i in range(m):
            img[(i, 1)] = tup[i]
            img[(i, -1)] = perm_inv(tup[i])
        nonconstant = len(set(img.values())) > 1
        p = word_prob_trivial(words, img)
        if nonconstant:
            if p > 1 - kappa:
                violations += 1
            if p > worst:
                worst, worst_tuple = p, tup
        else:
            constant_seen.append((tup, str(p)))
    return {"m": m, "L": L, "num_tuples": len(tuples), "kappa": str(kappa),
            "max_P_nonconstant": str(worst), "max_P_float": float(worst),
            "bound_1_minus_kappa": float(1 - kappa), "violations": violations,
            "worst_tuple": [list(t) for t in worst_tuple] if worst_tuple else None,
            "constant_assignments": [([list(t) for t in c[0]], c[1]) for c in constant_seen]}

def construction_words(m, r):
    A = letters(m)
    a = (0, 1)
    def red_words(length):
        out = []
        for w in itertools.product(A, repeat=length):
            if all(w[i + 1] != inv(w[i]) for i in range(length - 1)):
                out.append(w)
        return out
    xs = [x for x in red_words(r) if x[-1] not in (a, inv(a))]
    words = set()
    count = 0
    ok = True
    for x in xs:
        for y in xs:
            if y[0] == x[0]:
                continue
            for z in xs:
                if z[0] == y[0] or z[0] == x[0]:
                    continue
                xi = tuple(inv(c) for c in reversed(x))
                yi = tuple(inv(c) for c in reversed(y))
                zi = tuple(inv(c) for c in reversed(z))
                w = x + (a, a, a) + xi + y + (a, a, a) + yi + z + (a, a, a) + zi
                count += 1
                if len(w) != 6 * r + 9 or not is_cyclically_reduced(w):
                    ok = False
                words.add(w)
    lower = 2 * m * (2 * m - 1) * (2 * m - 2) * ((2 * m - 1) ** (r - 2) * (2 * m - 3)) ** 3 if r >= 2 else None
    return {"m": m, "r": r, "L": 6 * r + 9, "constructed": count, "distinct": len(words),
            "all_cyclically_reduced_of_length_6r+9": ok, "claimed_lower_bound": lower,
            "bound_holds": (lower is None) or (len(words) >= lower)}

def main():
    out = {}
    out["a_C_L"] = []
    for m, Lmax in ((2, 11), (3, 7)):
        for L in range(3, Lmax + 1):
            c = len(cr_words(m, L))
            out["a_C_L"].append({"m": m, "L": L, "count": c, "formula": C_formula(m, L), "match": c == C_formula(m, L)})
    out["b_transfer_formula"] = {"m=2": check_transfer(2, 10), "m=3": check_transfer(3, 8), "m=4": check_transfer(4, 6)}
    out["c_window"] = []
    for m, Lmax in ((2, 11), (3, 7)):
        bound = Fraction(m - 1, 2 * m * (2 * m - 1) ** 2)
        for L in range(3, Lmax + 1):
            words = cr_words(m, L)
            mn = None
            for x in letters(m):
                cnt = sum(1 for w in words if w[0] == x and w[2] == x)
                p = Fraction(cnt, len(words))
                mn = p if mn is None or p < mn else mn
            out["c_window"].append({"m": m, "L": L, "min_P": str(mn), "min_P_float": float(mn),
                                    "bound": str(bound), "bound_float": float(bound), "holds": mn >= bound})
    S3 = sorted(closure([(1, 0, 2), (1, 2, 0)]))
    S4 = sorted(closure([(1, 0, 2, 3), (1, 2, 3, 0)]))
    A5 = sorted(closure([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]))
    out["group_orders"] = {"S3": len(S3), "S4": len(S4), "A5": len(A5)}
    out["d_kappa"] = []
    for L in (3, 4, 5, 6, 7):
        out["d_kappa"].append(check_kappa(2, L, S3, list(itertools.product(S3, repeat=2))))
    for L in (5, 6, 7):
        out["d_kappa"].append(check_kappa(2, L, S4, list(itertools.product(S4, repeat=2))))
    rng = random.Random(20260913)
    tups = [tuple(rng.choice(A5) for _ in range(2)) for _ in range(150)]
    out["d_kappa"].append(check_kappa(2, 7, A5, tups))
    out["d_kappa"].append(check_kappa(3, 5, S3, list(itertools.product(S3, repeat=3))))
    out["e_alternating_generation"] = []
    for n in (5, 7, 9):
        c3 = tuple([1, 2, 0] + list(range(3, n)))
        cyc = tuple(list(range(1, n)) + [0])
        G = closure([c3, cyc])
        out["e_alternating_generation"].append({"n": n, "order": len(G), "half_factorial": math.factorial(n) // 2,
                                                 "equals_A_n": len(G) == math.factorial(n) // 2})
    out["f_construction"] = [construction_words(2, 2), construction_words(2, 3), construction_words(3, 2)]
    allok = (all(x["match"] for x in out["a_C_L"]) and all(out["b_transfer_formula"].values())
             and all(x["holds"] for x in out["c_window"]) and all(x["violations"] == 0 for x in out["d_kappa"])
             and all(x["equals_A_n"] for x in out["e_alternating_generation"])
             and all(x["distinct"] == x["constructed"] and x["all_cyclically_reduced_of_length_6r+9"] and x["bound_holds"]
                     for x in out["f_construction"]))
    out["ALL_OK"] = allok
    print(json.dumps(out, indent=1))

if __name__ == "__main__":
    main()
