"""Cube invariant for N sibling swap nodes in Toms's tower.

X = { psd Q : g+1 <= rank Q <= g+N }, covered by U_k = {lambda_(g+k) > lambda_(g+k+1)},
k = 1..N (lambda_(g+N+1) = 0 because rank <= g+N).  On U_full = U_1 cap ... cap U_N the
flag W = W_(g+1) < W_(g+2) < ... < W_(g+N) is continuous; ell_i = W_(g+i+1)/W_(g+i).
A class omega in H^q(U_full) sits in the top column E_1^(N-1,q) of the Mayer-Vietoris
spectral sequence and gives Omega in F^(N-1) H^(N-1+q)(X).

Model boundary map e on the boundary of the cube [-1,1]^N (times Y = prod CP^(j_nu)):
facet x_nu = +1 carries L_(nu,+) with c_1 = alpha u_nu, facet x_nu = -1 carries L_(nu,-)
with c_1 = beta u_nu.  e = 2 P_G + sum_a w_a P_a, weights w_(nu,+-) = max(0, +-x_nu - c)/(1-c).
The cover e^{-1}(U_k) of the sphere has as components of the N-fold intersection the
chambers (sigma, pi) of the barycentric subdivision of the cross-polytope:
sigma in {+-1}^N picks the side of each node, pi orders the N weights (largest first).
On chamber (sigma, pi):  W = G + L_(pi(1), sigma), ell_i = L_(pi(i+1), sigma).

This script
  1. checks the chamber combinatorics: every wall component (|T| = N-1) contains
     exactly two chambers, of opposite orientation sign(pi) prod(sigma); and checks that
     orientation against the determinant of the barycentric simplex;
  2. checks that classes pulled back from any U_T with |T| = N-1 have signed chamber
     sum 0 (so the value of omega is well defined on E_2 = E_infinity of the cover);
  3. evaluates omega = ch_(m_1)(W) prod_i y_i^(m_(i+1)) for N = 2, 3, 4 and compares with
        (1/m_1!) prod_k (alpha^m_k - beta^m_k) det[u_nu^(m_k)];
  4. reproduces the square value of toms-two-sibling-swap-drops-add-to-depth-two (N = 2);
  5. the alpha = -beta case: omega with odd exponents (1, 3, ...);
  6. limit lemma: brute force over all top-column monomials (with free Chern classes of G)
     for (N, j) = (2, 1), (3, 2), and (N, j, alpha=-beta) = (2, 2): every value is 0.
Run: python3 cube_invariant.py   (writes results.json next to it).
"""
import itertools
import json
import math
import os

import sympy as sp

al, be = sp.symbols("alpha beta")
U = sp.symbols("u1:6")
GS = sp.symbols("g1:24")  # ch_k(G), free symbols (arbitrary classes on Y)


def perm_sign(p):
    s, p = 1, list(p)
    for i in range(len(p)):
        while p[i] != i:
            k = p[i]
            p[i], p[k] = p[k], p[i]
            s = -s
    return s


def chambers(N):
    for sig in itertools.product((1, -1), repeat=N):
        for pi in itertools.permutations(range(N)):
            yield sig, pi


def orient(sig, pi):
    return perm_sign(pi) * math.prod(sig)


def line(nu, s):
    return (al if s == 1 else be) * U[nu]


def trunc(expr, js):
    """Reduce in H^*(prod CP^(j_nu)): kill u_nu^(j_nu+1). G symbols untouched."""
    expr = sp.expand(expr)
    if expr == 0:
        return expr
    gens = list(U[: len(js)])
    p = sp.Poly(expr, *gens)
    out = 0
    for mon, c in p.terms():
        if all(mon[i] <= js[i] for i in range(len(js))):
            out += c * sp.prod([gens[i] ** mon[i] for i in range(len(js))])
    return sp.expand(out)


# ---------- 1. combinatorics of the cover -------------------------------------------
def chain_of(sig, pi):
    """Full chain: tau_t = set of the top t lines, t = 1..N."""
    lines = [(pi[i], sig[pi[i]]) for i in range(len(pi))]
    return [frozenset(lines[:t]) for t in range(1, len(pi) + 1)]


def check_walls(N):
    walls = {}
    for sig, pi in chambers(N):
        ch = chain_of(sig, pi)
        for s in range(1, N + 1):  # drop size s: T = [N] \ {s}
            key = (s, tuple(ch[t - 1] for t in range(1, N + 1) if t != s))
            walls.setdefault(key, []).append(orient(sig, pi))
    ok = all(len(v) == 2 and sum(v) == 0 for v in walls.values())
    return ok, len(walls)


def check_orientation(N):
    ok = True
    for sig, pi in chambers(N):
        verts = []
        for k in range(1, N + 1):
            b = [0] * N
            for i in range(k):
                b[pi[i]] = sp.Rational(sig[pi[i]], k)
            verts.append(b)
        d = sp.Matrix(verts).det()
        ok &= (sp.sign(d) == orient(sig, pi) * sp.sign(sp.Matrix(
            [[sp.Rational(1, k) if i < k else 0 for i in range(N)] for k in range(1, N + 1)]).det()))
    return bool(ok)


# ---------- chamber sum -----------------------------------------------------------------
def ch_of_sum(k, xs, gk):
    """ch_k of G + sum of lines xs (gk = ch_k(G))."""
    return gk + sum(x ** k for x in xs) / sp.factorial(k)


def chamber_sum(N, omega_fn):
    tot = 0
    for sig, pi in chambers(N):
        xs = [line(pi[i], sig[pi[i]]) for i in range(N)]
        tot += orient(sig, pi) * omega_fn(xs)
    return sp.expand(tot)


def omega_monomial(ms):
    def f(xs):
        w = ch_of_sum(ms[0], [xs[0]], GS[ms[0] - 1] if ms[0] >= 1 else 1)
        return w * sp.prod([xs[i] ** ms[i] for i in range(1, len(ms))])
    return f


def formula(ms):
    N = len(ms)
    det = sp.Matrix(N, N, lambda k, nu: U[nu] ** ms[k]).det()
    return sp.expand(sp.prod([al ** m - be ** m for m in ms]) / sp.factorial(ms[0]) * det)


# ---------- 2. classes from U_T, |T| = N-1, vanish -------------------------------------
def check_wall_classes(N, trials=3):
    """For T = [N] minus {s}, U_T carries the block bundles W_(g+t_1), W_(g+t_2)/W_(g+t_1), ...
    Pull back products of ch_k of the blocks; the signed chamber sum must vanish."""
    import random
    random.seed(1)
    ok = True
    for s in range(1, N + 1):
        T = [t for t in range(1, N + 1) if t != s]
        for _ in range(trials):
            ks = [random.randint(1, 3) for _ in T]

            def f(xs, T=T, ks=ks):
                val, prev = 1, 0
                for idx, (t, k) in enumerate(zip(T, ks)):
                    block = xs[prev:t]
                    g = GS[k - 1] if idx == 0 else 0
                    val *= ch_of_sum(k, block, g)
                    prev = t
                return val
            ok &= chamber_sum(N, f) == 0
    return bool(ok)


# ---------- 6. limit lemma: all top-column monomials --------------------------------
def all_top_monomials(N, D):
    """Monomials prod_k ch_k(W)^(e_k) * prod_i y_i^(p_i) of complex degree 1..D."""
    out = []
    for p in itertools.product(range(D + 1), repeat=N - 1):
        rest = D - sum(p)
        if rest < 0:
            continue
        # partitions of the W-part degree into ch_k's
        def parts(n, kmax):
            if n == 0:
                yield []
                return
            for k in range(min(n, kmax), 0, -1):
                for q in parts(n - k, k):
                    yield [k] + q
        for dw in range(rest + 1):
            for lam in parts(dw, dw):
                if dw + sum(p) >= 1:
                    out.append((tuple(lam), p))
    return out


def monomial_fn(lam, p):
    def f(xs):
        v = 1
        for k in lam:
            v *= ch_of_sum(k, [xs[0]], GS[k - 1])
        for i, e in enumerate(p):
            v *= xs[i + 1] ** e
        return v
    return f


def limit_check(N, js, a, b):
    D = sum(js)
    mons = all_top_monomials(N, D)
    nz = 0
    for lam, p in mons:
        val = trunc(chamber_sum(N, monomial_fn(lam, p)).subs({al: a, be: b}), js)
        if val != 0:
            nz += 1
    return len(mons), nz


def admissible(js, a, b, odd_only=False):
    """Is there a system of distinct exponents m_k >= 1 and a bijection with m <= j_nu,
    alpha^m != beta^m?  Greedy on sorted j."""
    good = [m for m in range(1, max(js) + 1) if a ** m != b ** m]
    used, ok = set(), True
    for j in sorted(js):
        c = [m for m in good if m <= j and m not in used]
        if not c:
            ok = False
            break
        used.add(min(c))
    return ok


def main():
    res = {}
    # 1
    res["walls"] = {N: check_walls(N) for N in (2, 3, 4)}
    res["orientation_matches_det"] = {N: check_orientation(N) for N in (2, 3, 4)}
    # 2
    res["wall_classes_vanish"] = {N: check_wall_classes(N) for N in (2, 3, 4)}
    # 3
    fcheck = {}
    for ms in [(1, 2), (2, 1), (1, 3), (1, 2, 3), (2, 1, 3), (3, 1, 2), (1, 3, 5), (1, 2, 3, 4)]:
        N = len(ms)
        lhs = chamber_sum(N, omega_monomial(ms))
        fcheck[str(ms)] = bool(sp.expand(lhs - formula(ms)) == 0)
    res["formula_matches"] = fcheck
    # 4 square value of w5-113 (omega = c_1(W) y^2 = ch_1(W) y^2)
    sq = chamber_sum(2, omega_monomial((1, 2)))
    target = sp.expand((al - be) ** 2 * (al + be) * (U[0] * U[1] ** 2 - U[0] ** 2 * U[1]))
    res["square_value"] = str(sp.factor(sq))
    res["square_matches_up_to_sign"] = bool(sp.expand(sq - target) == 0 or sp.expand(sq + target) == 0)
    # N = 3 values
    n3 = {}
    for ms in [(1, 2, 3), (1, 3, 5)]:
        v = sp.factor(chamber_sum(3, omega_monomial(ms)))
        n3[str(ms)] = str(v)
        for (a, b) in [(1, 2), (-2, -1), (1, -1), (0, 0)]:
            for j in (2, 3, 5):
                n3[f"{ms} alpha={a} beta={b} j={j}"] = str(trunc(v.subs({al: a, be: b}), [j] * 3))
    res["N3_values"] = n3
    # 5 alpha = -beta, N = 2, exponents (1, 3)
    v = chamber_sum(2, omega_monomial((1, 3))).subs({al: 1, be: -1})
    res["alpha_minus_beta_N2_(1,3)"] = {f"j={j}": str(trunc(v, [j, j])) for j in (2, 3)}
    # 6 limit lemma (brute force)
    lim = {}
    for (N, js, a, b) in [(2, [1, 1], 1, 2), (3, [2, 2, 2], 1, 2), (2, [2, 2], 1, -1),
                          (3, [3, 3, 3], 1, 2), (2, [3, 3], 1, -1)]:
        tot, nz = limit_check(N, js, a, b)
        lim[f"N={N} j={js} alpha={a} beta={b}"] = {
            "monomials": tot, "nonzero": nz, "admissible_exponents": admissible(js, a, b)}
    res["limit_lemma"] = lim
    res["admissible_table_toms_(1,2)"] = {
        f"N={N} j={j}": admissible([j] * N, 1, 2) for N in range(1, 7) for j in range(1, 7)}
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "admissible_table_toms_(1,2)"}, indent=1))


if __name__ == "__main__":
    main()
