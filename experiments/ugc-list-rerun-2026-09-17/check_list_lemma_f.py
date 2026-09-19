#!/usr/bin/env python3
"""Checks for list-reference-constant-bias-decoding-loses-t-squared.

Toy doubled LEC: the plain Grassmann 2-to-1 game on F_2^n with one outer
vertex (label alpha in F_2^n, <lambda, x_e> = alpha . x_e).
  A-vertex p: l-dim subspace L, label sigma = functional on L.
  B-vertex q: (l-1)-dim subspace L', label tau = functional on L'.
  Constraint e = (L, L') for each hyperplane L' of L, uniform weight;
  pi_e(sigma) = sigma|L'; x_e = least point of L outside L'; ev_e = sigma(x_e).
A list is t references alpha^1..alpha^t (honest encodings, defect r = 0).
For each seed q a covering index i(q) is any i with tau_q = alpha^i|L'.

Checks
  (LF)  list Lemma F: for random and structured labellings H, random lists
        and random covering choices i(q),
          D_list <= beta_list + c_t,  c_t = min(t, 2^l - 1)/(2^l - 1),
        where D_list = mu{e in Sat(H): uncovered, or ev_e(sigma_p) !=
        alpha^{i(q)} . x_e} and beta_list = mu{e in Sat(H): uncovered}.
        Also the per-vertex form: at each p the covered, ev-dishonest
        satisfied mass is <= c_t (conditional on p).
  (T)   tightness of c_t: for every L, every sigma on L and every set of
        t <= 2^l - 1 nonzero functionals psi_j on L, the references
        restricting to sigma + psi_j and seeds tau_{ker psi_j} = sigma|ker
        give covered ev-dishonest satisfied conditional mass exactly
        t/(2^l - 1) at p.
Exit code 0 iff every check passes.
"""
import itertools, random, sys
from fractions import Fraction


def dot(a, b):
    return bin(a & b).count("1") & 1


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return frozenset(s)


def subspaces(n, k):
    out = set()
    for vecs in itertools.combinations(range(1, 2 ** n), k):
        S = span(vecs)
        if len(S) == 2 ** k:
            out.add(S)
    return sorted(out, key=lambda S: sorted(S))


def restrict(alpha, S):
    return tuple(dot(alpha, x) for x in sorted(S))


def build(n, l):
    A = subspaces(n, l)
    edges = []
    for pi, L in enumerate(A):
        for Lp in subspaces_of(L, l - 1):
            x = min(v for v in L if v not in Lp)
            edges.append((pi, Lp, x))
    return A, edges


def subspaces_of(L, k):
    pts = sorted(v for v in L if v)
    out = set()
    for vecs in itertools.combinations(pts, k):
        S = span(vecs)
        if len(S) == 2 ** k:
            out.add(S)
    return sorted(out, key=lambda S: sorted(S))


def eval_func(sigma, L, v):
    # sigma is a representative alpha in F_2^n; value on v in L
    return dot(sigma, v)


def check_LF(n, l, trials, rng):
    A, edges = build(n, l)
    kappa_den = 2 ** l - 1
    Bset = sorted({Lp for (_, Lp, _) in edges}, key=lambda S: sorted(S))
    fails = 0
    worst = Fraction(0)
    for trial in range(trials):
        t = rng.choice([1, 2, 3, 4, 2 ** l - 1, 2 ** l, 2 ** (l + 1)])
        refs = [rng.randrange(2 ** n) for _ in range(t)]
        mode = trial % 3
        # A-labels: representatives alpha_p (functional = restriction to L)
        if mode == 0:  # random labelling
            sig = [rng.randrange(2 ** n) for _ in A]
            tau = {Lp: rng.randrange(2 ** n) for Lp in Bset}
        elif mode == 1:  # seeds from random references, A-labels partners
            sig = [rng.choice(refs) ^ rng.randrange(2 ** n) for _ in A]
            tau = {Lp: rng.choice(refs) for Lp in Bset}
        else:  # A-labels: majority-consistent choice given seeds
            tau = {Lp: rng.choice(refs) for Lp in Bset}
            sig = []
            for L in A:
                best, bc = None, -1
                for a in rng.sample(range(2 ** n), min(2 ** n, 12)):
                    c = sum(restrict(a, Lp) == restrict(tau[Lp], Lp)
                            for Lp in subspaces_of(L, l - 1))
                    if c > bc:
                        best, bc = a, c
                sig.append(best)
        # covering choice i(q): random among covering refs
        cov = {}
        for Lp in Bset:
            opts = [i for i, a in enumerate(refs)
                    if restrict(a, Lp) == restrict(tau[Lp], Lp)]
            cov[Lp] = rng.choice(opts) if opts else None
        ct = Fraction(min(t, kappa_den), kappa_den)
        m = Fraction(1, len(edges))
        D = beta = Fraction(0)
        perp = {}
        for (pi, Lp, x) in edges:
            L = A[pi]
            sat = restrict(sig[pi], Lp) == restrict(tau[Lp], Lp)
            if not sat:
                continue
            i = cov[Lp]
            if i is None:
                beta += m
                D += m
                continue
            if dot(sig[pi], x) != dot(refs[i], x):
                D += m
                perp[pi] = perp.get(pi, 0) + 1
        if D > beta + ct:
            fails += 1
        for pi, c in perp.items():
            if Fraction(c, kappa_den) > ct:
                fails += 1
        worst = max(worst, D - beta - ct)
    return fails, worst


def check_T(n, l):
    A = subspaces(n, l)
    fails = 0
    cases = 0
    den = 2 ** l - 1
    for L in A[:6]:
        hyps = subspaces_of(L, l - 1)
        pts = sorted(L)
        # nonzero functionals on L, as representatives, one per restriction
        reps = {}
        for a in range(2 ** n):
            reps.setdefault(restrict(a, L), a)
        zero = restrict(0, L)
        nonzero = [a for r, a in reps.items() if r != zero]
        for sigma in list(reps.values())[:4]:
            for t in range(1, den + 1):
                for psis in itertools.combinations(nonzero, t):
                    cases += 1
                    refs = [sigma ^ p for p in psis]
                    bad = 0
                    for Lp in hyps:
                        # seed at L': covered by ref j iff psi_j vanishes on L'
                        js = [j for j, p in enumerate(psis)
                              if all(dot(p, v) == 0 for v in Lp)]
                        if not js:
                            continue
                        x = min(v for v in L if v not in Lp)
                        # H satisfied (tau = sigma|L'), covered by j,
                        # ev-dishonest iff psi_j(x) = 1, true off ker psi_j
                        if dot(sigma, x) != dot(refs[js[0]], x):
                            bad += 1
                    if Fraction(bad, den) != Fraction(t, den):
                        fails += 1
    return fails, cases


def main():
    rng = random.Random(20260917)
    ok = True
    for (n, l, tr) in [(3, 2, 300), (4, 2, 300), (4, 3, 120), (5, 3, 40)]:
        f, w = check_LF(n, l, tr, rng)
        print(f"(LF) n={n} l={l}: {tr} trials, failures={f}, "
              f"max(D - beta - c_t)={w}")
        ok &= f == 0
    for (n, l) in [(3, 2), (4, 2), (4, 3)]:
        f, c = check_T(n, l)
        print(f"(T)  n={n} l={l}: {c} cases, failures={f}")
        ok &= f == 0
    print("ALL PASS" if ok else "FAILURES")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
