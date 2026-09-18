#!/usr/bin/env python3
"""Independent checks of the analytic identities of
f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent (audit 2026-09-18, agent e2-w2-audit-f).

Nothing here is used in any proof; it is an adversarial re-derivation of the steps a referee cannot
check by eye.

(A) Theorem (1), the Koopman identity  E 2^{-|O_n|} = <Q^n 1_E, 1_E>,  Q = 1_E P 1_E on L^2({0,1}^X, m).
    Checked EXACTLY in rational arithmetic, by brute force over Omega = {0,1}^X and over all walk
    paths, for three finite transitive actions (S_3 on 3 points, S_4 on 4 points, Z/5 on itself),
    n <= 5.  A finite X is a legitimate test: proof section 1 uses nothing about X beyond transitivity
    of the action and symmetry of mu.

(B) Proof section 5.2-5.3, the Folner count on the ray: |x_0 Phi_N \ Phi_N| = |x_0^{-1} Phi_N \ Phi_N|
    = C(N-1, k-1) and |x_1^{+-1} Phi_N \ Phi_N| = 0, computed by enumerating k-subsets under the real
    dyadic maps, together with the resulting Rayleigh quotient bound 1 - k/N.

(C) Proof section 6.3, the dyadic depth bound d(g . 1/2) <= |g| + 2, by BFS over the ball of radius R
    in <x_0, x_1> acting on exact dyadics.

(D) Proof section 3.2-3.4 on a group where rho is known: the free group F_2 with mu uniform on the four
    generators, rho = sqrt(3)/2.  Checks that the ball-confined Perron eigenvalues lambda_R increase
    and stay below rho -- the engine of section 3 and of section 6.4.

Usage: python3 audit_koopman.py            (runtime well under a minute)
"""
import itertools
import math
from fractions import Fraction

FAIL = []
INV = {}


def report(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ((" | " + detail) if detail else ""), flush=True)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- (A) Koopman identity

def koopman_check(mult, act, points, base, mu, nmax):
    X = list(points)
    idx = {x: i for i, x in enumerate(X)}
    omegas = list(itertools.product((0, 1), repeat=len(X)))
    m = Fraction(1, 2 ** len(X))
    E = [w for w in omegas if w[idx[base]] == 0]
    Eset = set(E)

    # (g w)(x) = w(g^{-1} x), so (h^{-1} . w)(x) = w(h x).
    def push(h, w):
        return tuple(w[idx[act(h, X[i])]] for i in range(len(X)))

    vec = {w: Fraction(1) for w in E}
    lhs = []
    for _ in range(nmax):
        new = {}
        for w in E:
            s = Fraction(0)
            for h, p in mu.items():
                w2 = push(h, w)
                if w2 in Eset:
                    s += p * vec.get(w2, Fraction(0))
            if s:
                new[w] = s
        vec = new
        lhs.append(sum(vec.values()) * m)

    rhs = []
    for n in range(1, nmax + 1):
        tot = Fraction(0)
        for path in itertools.product(list(mu.items()), repeat=n):
            p = Fraction(1)
            g = None
            O = {base}
            for h, q in path:
                p *= q
                g = h if g is None else mult(h, g)          # g_k = h_k ... h_1
                O.add(act(INV[g], base))
            tot += p * Fraction(1, 2 ** len(O))
        rhs.append(tot)
    return lhs, rhs


def perm_group(n, gens):
    idg = tuple(range(n))
    seen = {idg}
    frontier = [idg]
    while frontier:
        g = frontier.pop()
        for s in gens:
            h = tuple(s[g[i]] for i in range(n))
            if h not in seen:
                seen.add(h)
                frontier.append(h)
    return sorted(seen)


def run_A():
    cases = [
        ("S3 on 3 points", 3, [(1, 0, 2), (0, 2, 1), (2, 1, 0)]),
        ("S4 on 4 points", 4, [(1, 0, 2, 3), (0, 2, 1, 3), (0, 1, 3, 2)]),
        ("Z/5 regular", 5, [tuple((i + 1) % 5 for i in range(5)),
                            tuple((i - 1) % 5 for i in range(5))]),
    ]
    for name, n, gens in cases:
        G = perm_group(n, gens)

        def mult(a, b, n=n):
            return tuple(a[b[i]] for i in range(n))

        INV.clear()
        for g in G:
            h = [0] * n
            for i in range(n):
                h[g[i]] = i
            INV[g] = tuple(h)
        mu = {g: Fraction(1, len(gens)) for g in gens}
        assert all(INV[g] in mu for g in mu), "mu must be symmetric"
        lhs, rhs = koopman_check(mult, lambda g, x: g[x], range(n), 0, mu, 5)
        report("A: Koopman identity, " + name, lhs == rhs,
               "n=1..5: " + ", ".join(str(v) for v in lhs))


# ---------------------------------------------------------------- (B) Folner count on the ray

def dy_x0(t):
    if t <= Fraction(1, 2):
        return t / 2
    if t <= Fraction(3, 4):
        return t - Fraction(1, 4)
    return 2 * t - 1


def dy_x0i(t):
    if t <= Fraction(1, 4):
        return 2 * t
    if t <= Fraction(1, 2):
        return t + Fraction(1, 4)
    return (t + 1) / 2


def dy_x1(t):
    if t <= Fraction(1, 2):
        return t
    if t <= Fraction(3, 4):
        return t / 2 + Fraction(1, 4)
    if t <= Fraction(7, 8):
        return t - Fraction(1, 8)
    return 2 * t - 1


def dy_x1i(t):
    if t <= Fraction(1, 2):
        return t
    if t <= Fraction(5, 8):
        return 2 * t - Fraction(1, 2)
    if t <= Fraction(3, 4):
        return t + Fraction(1, 8)
    return (t + 1) / 2


GENS = [("x0", dy_x0), ("x0i", dy_x0i), ("x1", dy_x1), ("x1i", dy_x1i)]


def run_B():
    ok_all = True
    detail = []
    for N in (5, 6, 7, 8):
        ray = [Fraction(1, 2 ** j) for j in range(1, N + 1)]
        for k in range(1, min(N, 4) + 1):
            Phi = set(frozenset(S) for S in itertools.combinations(ray, k))
            counts = {}
            hits = 0
            for nm, f in GENS:
                img = set(frozenset(f(t) for t in S) for S in Phi)
                counts[nm] = len(img - Phi)
                hits += len(img & Phi)
            want = math.comb(N - 1, k - 1)
            ok = (counts["x0"] == want and counts["x0i"] == want
                  and counts["x1"] == 0 and counts["x1i"] == 0)
            rq = Fraction(hits, 4 * len(Phi))
            ok_all &= ok and (rq >= 1 - Fraction(k, N))
            if N == 8:
                detail.append("N=8 k=%d shed=%d C(N-1,k-1)=%d rayleigh=%.4f >= %.4f"
                              % (k, counts["x0"], want, float(rq), 1 - k / N))
    report("B: ray Folner counts and Rayleigh bound 1-k/N", ok_all, "; ".join(detail))


# ---------------------------------------------------------------- (C) dyadic depth

def depth(t):
    return max(1, t.denominator.bit_length() - 1)


def run_C():
    R = 7
    dist = {Fraction(1, 2): 0}
    cur = [Fraction(1, 2)]
    worst = {}
    for r in range(1, R + 1):
        nxt = []
        for t in cur:
            for _, f in GENS:
                s = f(t)
                if s not in dist:
                    dist[s] = r
                    nxt.append(s)
        cur = nxt
        worst[r] = max(depth(t) for t in dist if dist[t] <= r)
    ok = all(worst[r] <= r + 2 for r in worst)
    report("C: d(g.1/2) <= |g|+2 for |g| <= %d" % R, ok,
           "max depth by radius: " + ", ".join("%d:%d" % (r, worst[r]) for r in sorted(worst)))


# ---------------------------------------------------------------- (D) ball Perron eigenvalues

def run_D():
    def redmul(s, w):
        if w and w[0] == -s:
            return w[1:]
        return (s,) + w

    lam = []
    for R in range(1, 6):
        ball = [()]
        seen = {()}
        frontier = [()]
        for _ in range(R):
            nxt = []
            for w in frontier:
                for s in (1, -1, 2, -2):
                    u = redmul(s, w)
                    if u not in seen:
                        seen.add(u)
                        ball.append(u)
                        nxt.append(u)
            frontier = nxt
        idx = {w: i for i, w in enumerate(ball)}
        n = len(ball)
        adj = [[] for _ in range(n)]          # sparse: 4 nonzeros per column
        for w in ball:
            for s in (1, -1, 2, -2):
                u = redmul(s, w)
                if u in idx:
                    adj[idx[u]].append(idx[w])
        v = [1.0] * n
        val = 0.0
        for _ in range(3000):
            nv = [0.25 * sum(v[j] for j in row) for row in adj]
            nrm = math.sqrt(sum(x * x for x in nv))
            if nrm == 0:
                break
            v = [x / nrm for x in nv]
            val = nrm
        lam.append(val)
    rho = math.sqrt(3) / 2
    ok = (all(lam[i] <= lam[i + 1] + 1e-9 for i in range(len(lam) - 1))
          and all(x <= rho + 1e-9 for x in lam))
    report("D: F_2 ball Perron eigenvalues increase, stay <= rho=%.6f" % rho, ok,
           "lambda_R = " + ", ".join("%.5f" % x for x in lam))


if __name__ == "__main__":
    run_A()
    run_B()
    run_C()
    run_D()
    print()
    print("ALL PASS" if not FAIL else "FAILURES: " + ", ".join(FAIL))
