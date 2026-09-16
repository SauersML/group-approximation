#!/usr/bin/env python3
"""Sanity checks for nested permutable rounding of Galois unique games.

Date: 2026-09-16.  Lane hi-spec-unique-games-conjecture.

Notation of research/galois-unique-game-value-is-transversal-expansion.md:
Gal(G,K,mu) has value max_T Pr_(t in T, s ~ mu)[s t in T] over left transversals
T of K.  The checks, on small permutation groups G, fibres K and random
symmetric conjugation-invariant mu, are:

  (N1) Lemma B (nested chains): for a chain G = P_0 >= P_1 >= ... >= P_s = L with
       (K cap P_(j-1)) P_j a subgroup for every j and K cap L = {e}, the
       recursive construction outputs a left transversal T of K that is a union
       of left L-cosets, and Phi(T) = Pr[s t in T] >= mu(L).
  (N2) brute-force val >= max mu(L) over all nested chains.
  (N3) Theorem C of research/artifacts/ugc-nested-permutable-rounding-2026-09-16.md
       (claim galois-rounding-pays-fibre-orbits-above-abelian-normal): with
       d = min over abelian normal A of max over subgroups Q >= A of
       [K : N_K(Q)], and a numerically feasible certificate phi = f * f~
       (phi(e) = 1, phi = 0 on K minus e) with sum mu phi = 1 - eps,
       max nested mu(L) >= 1 - 3 eps d log_q k / c(G,m).  "covered" means d = 1.

This is evidence only (tiny groups, numerical certificates), not a proof.
Run: timeout 600 python3 check_nested_rounding.py
"""
import itertools
import math
import os
import random

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import numpy as np
from scipy.optimize import minimize


# ---------------------------------------------------------------- groups ----
def compose(p, q):
    """(p q)(i) = p(q(i)): apply q first."""
    return tuple(p[i] for i in q)


def inverse(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def closure(gens, n):
    e = tuple(range(n))
    elems = {e}
    frontier = [e]
    gens = list(gens)
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = compose(g, x)
                if y not in elems:
                    elems.add(y)
                    new.append(y)
        frontier = new
    return frozenset(elems)


def cyc(n, *cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)


def order(p):
    e = tuple(range(len(p)))
    x, r = p, 1
    while x != e:
        x, r = compose(p, x), r + 1
    return r


def subgroups(G, n):
    """All subgroups, by repeated joins of cyclic subgroups (complete)."""
    cyclic = {closure([g], n) for g in G}
    subs = set(cyclic)
    frontier = list(subs)
    while frontier:
        new = []
        for H in frontier:
            for C in cyclic:
                if C <= H:
                    continue
                J = closure(list(H) + list(C), n)
                if J not in subs:
                    subs.add(J)
                    new.append(J)
        frontier = new
    return sorted(subs, key=len)


def prod_set(X, Y):
    return frozenset(compose(x, y) for x in X for y in Y)


def is_permutable(X, Y):
    return prod_set(X, Y) == prod_set(Y, X)


def normalizes(K, H):
    return all(frozenset(compose(compose(a, h), inverse(a)) for h in H) == H for a in K)


def is_normal(G, H):
    return normalizes(G, H)


def is_abelian(H):
    return all(compose(x, y) == compose(y, x) for x in H for y in H)


# ------------------------------------------------------------- measures ----
def classes(G):
    left = set(G)
    out = []
    while left:
        g = next(iter(left))
        C = frozenset(compose(compose(x, g), inverse(x)) for x in G)
        out.append(C)
        left -= C
    return out


def random_mu(G, rng):
    e = tuple(range(len(next(iter(G)))))
    cls = [C for C in classes(G) if e not in C]
    merged, seen = [], set()
    for C in cls:
        if C in seen:
            continue
        Ci = frozenset(inverse(x) for x in C)
        U = C | Ci
        seen.add(C)
        seen.add(Ci)
        merged.append(U)
    delta = rng.uniform(0.01, 0.25)
    pick = [U for U in merged if rng.random() < 0.5] or [rng.choice(merged)]
    w = [rng.random() for _ in pick]
    tot = sum(w)
    mu = {g: 0.0 for g in G}
    mu[e] = 1 - delta
    for U, wi in zip(pick, w):
        for g in U:
            mu[g] += delta * wi / tot / len(U)
    return mu


def mass(mu, X):
    return sum(mu[g] for g in X)


# ---------------------------------------------------------------- values ----
def left_cosets(G, H):
    left, out = set(G), []
    while left:
        g = next(iter(left))
        C = frozenset(compose(g, h) for h in H)
        out.append(C)
        left -= C
    return out


def phi_T(T, mu):
    T = set(T)
    supp = [(s, w) for s, w in mu.items() if w > 0]
    acc = 0.0
    for t in T:
        for s, w in supp:
            if compose(s, t) in T:
                acc += w
    return acc / len(T)


def brute_val(G, K, mu):
    cos = [sorted(C) for C in left_cosets(G, K)]
    best = -1.0
    for choice in itertools.product(*cos):
        v = phi_T(choice, mu)
        if v > best:
            best = v
    return best


# ------------------------------------------------------- nested chains ----
def best_nested(G, K, subs, mu):
    memo = {}

    def rec(P):
        if P in memo:
            return memo[P]
        KP = K & P
        if len(KP) == 1:
            memo[P] = (mass(mu, P), [P])
            return memo[P]
        best = (-1.0, None)
        for Q in subs:
            if len(Q) < len(P) and Q < P and is_permutable(KP, Q):
                v, ch = rec(Q)
                if v > best[0]:
                    best = (v, [P] + ch)
        memo[P] = best
        return best

    return rec(frozenset(G))


def best_permutable(G, K, subs, mu):
    best = (-1.0, None)
    for L in subs:
        if len(K & L) == 1 and is_permutable(K, L):
            v = mass(mu, L)
            if v > best[0]:
                best = (v, L)
    return best


def nested_transversal(K, chain):
    """Lemma B construction: T_s = L; T_(j-1) = union over r in R of r T_j."""
    T = set(chain[-1])
    for j in range(len(chain) - 1, 0, -1):
        P0, P1 = chain[j - 1], chain[j]
        M = prod_set(K & P0, P1)
        R = [min(C) for C in left_cosets(P0, M)]
        T = {compose(r, t) for r in R for t in T}
    return T


def is_left_transversal(G, K, T):
    return all(len(C & T) == 1 for C in left_cosets(G, K))


def union_of_left_cosets(T, L):
    return all(compose(t, l) in T for t in T for l in L)


# ----------------------------------------------------- SDP certificates ----
def feasible_certificate(G, K, mu, rng, restarts=12):
    """Numerically feasible phi = f * f~ with phi(e)=1, phi = 0 on K minus e.

    Returns (sum mu phi, max constraint residual).  Any feasible phi is a valid
    hypothesis for (N3); optimality is not needed.
    """
    elems = sorted(G)
    idx = {g: i for i, g in enumerate(elems)}
    n = len(elems)
    e = tuple(range(len(elems[0])))
    # A[g][y] = index of g^-1 y, B[g][y] = index of g y
    A = {g: np.array([idx[compose(inverse(g), y)] for y in elems]) for g in elems}
    Bm = {g: np.array([idx[compose(g, y)] for y in elems]) for g in elems}
    w = np.array([mu[g] for g in elems])
    # phi is real and phi(a^-1) = phi(a), so keep one constraint per pair
    # {a, a^-1}; duplicated equality constraints make SLSQP rank-deficient.
    Kx, seenK = [], set()
    for a in sorted(K):
        if a != e and a not in seenK:
            Kx.append(a)
            seenK.add(a)
            seenK.add(inverse(a))

    def phi(f, g):
        return float(f[A[g]] @ f)

    def gphi(f, g):
        return f[A[g]] + f[Bm[g]]

    def obj(f):
        return -sum(w[i] * phi(f, g) for i, g in enumerate(elems) if w[i] > 0)

    def gobj(f):
        out = np.zeros(n)
        for i, g in enumerate(elems):
            if w[i] > 0:
                out -= w[i] * gphi(f, g)
        return out

    cons = [{"type": "eq", "fun": lambda f: f @ f - 1.0, "jac": lambda f: 2 * f}]
    for a in Kx:
        cons.append({"type": "eq", "fun": (lambda f, a=a: phi(f, a)),
                     "jac": (lambda f, a=a: gphi(f, a))})
    best = (-1.0, 1.0)
    for _ in range(restarts):
        f0 = np.array([rng.gauss(0, 1) for _ in range(n)])
        f0 /= np.linalg.norm(f0)
        res = minimize(obj, f0, jac=gobj, constraints=cons, method="SLSQP",
                       options={"maxiter": 400, "ftol": 1e-12})
        f = res.x / np.linalg.norm(res.x)
        resid = max([abs(phi(f, a)) for a in Kx] + [0.0])
        val = -obj(f)
        if resid < 1e-7 and val > best[0]:
            best = (val, resid)
    return best


# ------------------------------------------------------------ hypothesis ----
def hypothesis_witness(G, K, subs):
    """Some abelian normal A such that K normalizes every subgroup containing A."""
    for A in subs:
        if is_abelian(A) and is_normal(G, A):
            if all(normalizes(K, H) for H in subs if A <= H):
                central = all(compose(compose(a, g), compose(inverse(a), inverse(g))) in A
                              for a in K for g in G)
                return A, central, K <= A
    return None, False, False


def orbit_defect(G, K, subs):
    """min over abelian normal A of max over Q >= A of [K : N_K(Q)]."""
    best = None
    for A in subs:
        if is_abelian(A) and is_normal(G, A):
            d = 1
            for Q in subs:
                if A <= Q:
                    NK = [a for a in K if frozenset(compose(compose(a, h), inverse(a)) for h in Q) == Q]
                    d = max(d, len(K) // len(NK))
            if best is None or d < best[0]:
                best = (d, A)
    return best


def least_prime(k):
    p = 2
    while k % p:
        p += 1
    return p


# ------------------------------------------------------------------ main ----
def wreath_f2_f2sq():
    n = 8
    gens = [cyc(n, (2 * i, 2 * i + 1)) for i in range(4)]
    tops = []
    for t in (1, 2):
        p = [0] * n
        for i in range(4):
            for b in (0, 1):
                p[2 * i + b] = 2 * (i ^ t) + b
        tops.append(tuple(p))
    G = closure(gens + tops, n)
    K = closure(tops, n)
    return G, K, n


def cases():
    out = []
    n = 3
    out.append(("S3, K=<(01)>", closure([cyc(n, (0, 1)), cyc(n, (0, 1, 2))], n), closure([cyc(n, (0, 1))], n), n, True))
    n = 4
    out.append(("A4, K=<(012)>", closure([cyc(n, (0, 1, 2)), cyc(n, (0, 1), (2, 3))], n), closure([cyc(n, (0, 1, 2))], n), n, True))
    n = 6
    out.append(("D12, K=<reflection>", closure([cyc(n, (0, 1, 2, 3, 4, 5)), cyc(n, (1, 5), (2, 4))], n), closure([cyc(n, (1, 5), (2, 4))], n), n, True))
    n = 7
    b = cyc(n, (1, 2), (3, 4, 5, 6))
    out.append(("Dic12, K=<b> order 4", closure([cyc(n, (0, 1, 2)), b], n), closure([b], n), n, True))
    n = 6
    sw = cyc(n, (0, 3), (1, 4), (2, 5))
    out.append(("F3 wr Z2, K=<swap>", closure([cyc(n, (0, 1, 2)), cyc(n, (3, 4, 5)), sw], n), closure([sw], n), n, True))
    top = cyc(n, (0, 2, 4), (1, 3, 5))
    out.append(("F2 wr Z3, K=<top>", closure([cyc(n, (0, 1)), cyc(n, (2, 3)), cyc(n, (4, 5)), top], n), closure([top], n), n, True))
    n = 4
    S4 = closure([cyc(n, (0, 1)), cyc(n, (0, 1, 2, 3))], n)
    out.append(("S4, K=<(012)>", S4, closure([cyc(n, (0, 1, 2))], n), n, True))
    out.append(("S4, K=<(01)>", S4, closure([cyc(n, (0, 1))], n), n, True))
    G, K, n = wreath_f2_f2sq()
    out.append(("F2 wr F2^2, K=T (order 4)", G, K, n, False))
    return out


def main():
    rng = random.Random(20260916)
    fails = {"N1": 0, "N2": 0, "N3": 0}
    nested_beats_permutable = 0
    for name, G, K, n, do_val in cases():
        subs = subgroups(G, n)
        e = tuple(range(n))
        exps = [order(g) for g in G]
        m = 1
        for x in exps:
            m = m * x // math.gcd(m, x)
        k = len(K)
        q = least_prime(k)
        c = min(1 - math.cos(2 * math.pi / m), 1 - 2 ** -0.5)  # all test groups solvable
        A, central, inA = hypothesis_witness(G, K, subs)
        covered = A is not None
        dA, Ad = orbit_defect(G, K, subs)
        print(f"== {name}: |G|={len(G)} k={k} m={m} #subgroups={len(subs)} "
              f"covered={covered} (|A|={len(A) if A else '-'}, [K,G]<=A: {central}, K<=A: {inA}) "
              f"d_A(K)={dA} at |A|={len(Ad)}")
        assert covered == (dA == 1)
        trials = 4 if do_val else 2
        for _ in range(trials):
            mu = random_mu(G, rng)
            vN, chain = best_nested(G, K, subs, mu)
            vP, _L = best_permutable(G, K, subs, mu)
            if vN > vP + 1e-12:
                nested_beats_permutable += 1
            T = nested_transversal(K, chain)
            L = chain[-1]
            ok1 = is_left_transversal(G, K, T) and union_of_left_cosets(T, L) and phi_T(T, mu) >= mass(mu, L) - 1e-12
            fails["N1"] += (not ok1)
            line = f"   nested mu(L)={vN:.4f} permutable mu(L)={vP:.4f} chain_len={len(chain)-1} Phi(T)={phi_T(T, mu):.4f} N1={ok1}"
            if do_val:
                val = brute_val(G, K, mu)
                ok2 = val >= vN - 1e-12
                fails["N2"] += (not ok2)
                line += f" val={val:.4f} N2={ok2}"
            sdp, resid = feasible_certificate(G, K, mu, rng)
            eps = 1 - sdp
            bound = 1 - 3 * eps * dA * math.log(k, q) / c
            line += f" cert={sdp:.4f} (resid {resid:.1e})"
            if sdp >= 0:
                ok3 = vN >= bound - 1e-9
                fails["N3"] += (not ok3)
                line += f" bound={bound:.4f} N3={ok3} ratio(1-muL)/eps={(1 - vN) / max(eps, 1e-12):.3f}"
            else:
                line += " N3=vacuous(no certificate found)"
            print(line)
    print("failures", fails, "nested>permutable instances", nested_beats_permutable)


if __name__ == "__main__":
    main()
