#!/usr/bin/env python3
"""Checks for the CDF rigidity lemma and the ceiling on the order-1 scale-limit functional (E2).

Node: research/thompson-f-markov-size-chain-scale-limit-affinity-at-most-0-978.md

Set-up (E2) of research/thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit.md: a
stationary order-1 chain X_t on [0,1], marginal pi, forward rows f_m, reversed rows r_m,
  U(m) = r_m([0,m)),  D(m) = f_m([0,m)),  S = U + D,
  A(m) = E[1{X_-1<m} BC(r_X-1, r_m)^2 | X_0=m] + E[1{X_1<m} BC(f_X1, f_m)^2 | X_0=m],
  B = E_pi sqrt(A).
Lemma: with Delta_up = E[U(1-D)] - E[U^2]/2 and Delta_dn = E[D(1-U)] - E[D^2]/2,
  |Delta_up| <= delta_up = E[1{X_-1<X_0} TV(r_X-1, r_X0)],
  |Delta_dn| <= delta_dn = E[1{X_1<X_0} TV(f_X1, f_X0)],
hence Var(S) >= 1/3 - (4/3)(delta_up + delta_dn), and B <= 0.98066.

Part 1 checks each identity exactly on random N-bin kernels. The identities are evaluated from their
two sides independently: the left sides are computed over pairs (X_-1, X_0), and the right sides from
U and D alone. Part 1 also cross-checks B against scale_B of the 2026-09-17 census.
Part 2 checks every inequality at L-BFGS optima of B, which are near-extremal kernels.
Part 3 evaluates the closed-form ceiling and a rigorous cell-wise upper bound on the Lagrangian dual
of the relaxation.
"""
import sys
import os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "thompson-f-markov-forest-2026-09-17"))

# Gauss-Legendre on [0,1] (exact for the polynomials in t used below)
GX, GW = np.polynomial.legendre.leggauss(8)
GX = (GX + 1) / 2
GW = GW / 2


def stationary_np(P):
    w, v = np.linalg.eig(P.T)
    k = np.argmin(abs(w - 1))
    p = np.real(v[:, k])
    return p / p.sum()


def quantities(P):
    """Everything for a bin kernel P (row-stochastic, N equal bins, uniform inside bins)."""
    N = P.shape[0]
    pi = stationary_np(P)
    R = (pi[None, :] * P.T) / pi[:, None]          # R[j,i] = pi_i P_ij / pi_j  (reversed row of bin j)
    BCr = np.sqrt(R) @ np.sqrt(R).T
    BCf = np.sqrt(P) @ np.sqrt(P).T
    TVr = 0.5 * abs(R[:, None, :] - R[None, :, :]).sum(2)
    TVf = 0.5 * abs(P[:, None, :] - P[None, :, :]).sum(2)
    low = np.tril(np.ones((N, N)), -1)             # low[j,i] = 1 iff i < j
    cumR = (R * low).sum(1)                        # sum_{i<j} R_ji
    cumP = (P * low).sum(1)

    def U(j, t):
        return cumR[j] + R[j, j] * t

    def D(j, t):
        return cumP[j] + P[j, j] * t

    def Fr(j, i, t):                               # r_{bin j}([0, s)) for s in bin i at position t
        return R[j, :i].sum() + R[j, i] * t

    def Ff(j, i, t):
        return P[j, :i].sum() + P[j, i] * t

    E = lambda g: sum(pi[j] * (GW * g(j, GX)).sum() for j in range(N))     # E_pi over m
    # right-hand sides, from U and D only
    EU = E(U); ED = E(D)
    ES = E(lambda j, t: U(j, t) + D(j, t))
    ES2 = E(lambda j, t: (U(j, t) + D(j, t)) ** 2)
    rhs_i_up = E(lambda j, t: U(j, t) * (1 - D(j, t)))
    rhs_ii_up = E(lambda j, t: U(j, t) ** 2) / 2
    rhs_i_dn = E(lambda j, t: D(j, t) * (1 - U(j, t)))
    rhs_ii_dn = E(lambda j, t: D(j, t) ** 2) / 2
    # left-hand sides, over pairs: X_-1 in bin i at t, X_0 in bin j at t', prob pi_i P_ij, t,t' iid U[0,1]
    lhs_i_up = lhs_ii_up = lhs_i_dn = lhs_ii_dn = 0.0
    delta_up = delta_dn = 0.0
    for i in range(N):
        for j in range(N):
            if i < j:        # up-step X_-1 < X_0 surely
                lhs_i_up += pi[i] * P[i, j] * (GW * U(i, GX)).sum()
                lhs_ii_up += pi[i] * P[i, j] * (GW * Fr(j, i, GX)).sum()
                delta_up += pi[i] * P[i, j] * TVr[i, j]
                # down-step X_1 < X_0 with X_0 in bin j, X_1 in bin i: prob pi_j P_ji
                lhs_i_dn += pi[j] * P[j, i] * (GW * D(i, GX)).sum()
                lhs_ii_dn += pi[j] * P[j, i] * (GW * Ff(j, i, GX)).sum()
                delta_dn += pi[j] * P[j, i] * TVf[i, j]
            elif i == j:     # same bin: X_-1 < X_0 iff t < t'  (weight 1 - t);  TV = 0
                lhs_i_up += pi[i] * P[i, i] * (GW * U(i, GX) * (1 - GX)).sum()
                lhs_ii_up += pi[i] * P[i, i] * (GW * Fr(i, i, GX) * (1 - GX)).sum()
                lhs_i_dn += pi[i] * P[i, i] * (GW * D(i, GX) * (1 - GX)).sum()
                lhs_ii_dn += pi[i] * P[i, i] * (GW * Ff(i, i, GX) * (1 - GX)).sum()
    # B and a
    alpha = np.array([(R[j] * low[j] * BCr[j] ** 2).sum() + (P[j] * low[j] * BCf[j] ** 2).sum() for j in range(N)])
    beta = np.diag(R) + np.diag(P)
    Bv = sum(pi[j] * (2.0 / 3.0) * ((alpha[j] + beta[j]) ** 1.5 - alpha[j] ** 1.5) / beta[j] for j in range(N))
    a = np.array([(R[j] * low[j] * TVr[j] ** 2).sum() + (P[j] * low[j] * TVf[j] ** 2).sum() for j in range(N)])
    Ea = (pi * a).sum()
    Esqrt_S = E(lambda j, t: np.sqrt(U(j, t) + D(j, t)))    # (smooth integrand; 8-point GL)
    return dict(pi=pi, EU=EU, ED=ED, ES=ES, VarS=ES2 - ES ** 2, B=Bv, Ea=Ea, EsqrtS=Esqrt_S,
                i_up=(lhs_i_up, rhs_i_up), ii_up=(lhs_ii_up, rhs_ii_up),
                i_dn=(lhs_i_dn, rhs_i_dn), ii_dn=(lhs_ii_dn, rhs_ii_dn),
                Dup=rhs_i_up - rhs_ii_up, Ddn=rhs_i_dn - rhs_ii_dn,
                dup=delta_up, ddn=delta_dn)


KAPPA = (3 - 2 * np.sqrt(2)) / 2


def ceiling(x):
    return 1 - KAPPA * max(0.0, 1 / 3 - 4 * x / 3) - x * x / (2 * np.sqrt(2))


def report(q, tag):
    worst = max(abs(q[k][0] - q[k][1]) for k in ("i_up", "ii_up", "i_dn", "ii_dn"))
    d = q["dup"] + q["ddn"]
    x = np.sqrt(q["Ea"])
    ok = (abs(q["Dup"]) <= q["dup"] + 1e-12 and abs(q["Ddn"]) <= q["ddn"] + 1e-12
          and q["VarS"] >= 1 / 3 - 4 * d / 3 - 1e-12 and d <= x + 1e-12
          and q["B"] <= q["EsqrtS"] - q["Ea"] / (2 * np.sqrt(2)) + 1e-9
          and q["EsqrtS"] <= 1 - KAPPA * q["VarS"] + 1e-9 and q["B"] <= ceiling(x) + 1e-9)
    print("%-14s ES=%.12f  max|lhs-rhs|=%.1e  |Dup|=%.4f<=dup=%.4f  |Ddn|=%.4f<=ddn=%.4f  "
          "VarS=%.4f>=%.4f  delta=%.4f<=sqrtEa=%.4f  B=%.6f<=ceil(x)=%.6f  %s"
          % (tag, q["ES"], worst, abs(q["Dup"]), q["dup"], abs(q["Ddn"]), q["ddn"], q["VarS"],
             1 / 3 - 4 * d / 3, d, x, q["B"], ceiling(x), "OK" if ok else "FAIL"), flush=True)
    return ok and worst < 1e-12


def part1():
    print("== Part 1: identities (i),(ii) exactly on random bin kernels ==")
    rng = np.random.default_rng(1)
    allok = True
    try:
        import torch
        from scale_limit import scale_B
        torch.set_default_dtype(torch.float64)
    except Exception as e:      # noqa
        scale_B = None
        print("scale_B cross-check unavailable:", e)
    for trial in range(12):
        N = [2, 3, 5, 8][trial % 4]
        P = rng.gamma([0.3, 1.0, 3.0][trial % 3], size=(N, N))
        P /= P.sum(1, keepdims=True)
        q = quantities(P)
        allok &= report(q, "rand N=%d" % N)
        if scale_B is not None:
            b2 = float(scale_B(torch.tensor(P)))
            print("   scale_B cross-check |B - scale_B| = %.1e" % abs(q["B"] - b2))
            allok &= abs(q["B"] - b2) < 1e-10
    # product kernel: tight case S = 2u, Var = 1/3, delta = 0
    N = 6
    p = rng.dirichlet(np.ones(N))
    q = quantities(np.tile(p, (N, 1)))
    allok &= report(q, "product")
    print("   product: VarS=%.12f (1/3), B=%.12f (2sqrt2/3=%.12f)" % (q["VarS"], q["B"], 2 * 2 ** .5 / 3))
    return allok


def part2():
    print("== Part 2: inequalities at L-BFGS optima of B (near-extremal kernels) ==")
    import torch
    from scale_limit import scale_B
    from markov_ansatz import opt
    torch.set_default_dtype(torch.float64)
    torch.manual_seed(0)
    allok = True
    for N in [4, 8, 16]:
        v, L = opt(lambda z: scale_B(torch.softmax(z, 1)), 0.5 * torch.randn(N, N), iters=1500)
        P = torch.softmax(L, 1).detach().numpy()
        allok &= report(quantities(P), "opt N=%d" % N)
    return allok


def part3():
    print("== Part 3: closed-form ceiling and cell-certified dual ==")
    xs = 4 * np.sqrt(2) * KAPPA / 3
    closed = 1 - (3 - 2 * np.sqrt(2)) / 6 + 4 * (17 - 12 * np.sqrt(2)) / (9 * np.sqrt(2))
    grid = np.linspace(0, 1.5, 150001)
    print("closed form: x*=%.6f  ceiling=%.8f  grid max=%.8f  (x>1/4 branch <= %.6f)  R<=%.6f"
          % (xs, closed, max(ceiling(x) for x in grid[::10]), 1 - 1 / (16 * 2 * np.sqrt(2)), (1 + closed) / 2))
    # dual of: max E sqrt(S-a) s.t. E S = 1, E[S - 3/4 S^2] <= E sqrt(S a), 0<=a<=S<=2.
    # V(l0,l) = l0 + max_S [ sqrt(S + l^2 S^2) - (l0+l) S + 3/4 l S^2 ] is an upper bound for every
    # l0 real, l >= 0 (weak duality; the a-maximum is Cauchy-Schwarz).  The S-max is certified on
    # cells [S_k, S_k+1]: the increasing parts are evaluated at S_k+1, the decreasing one at S_k.
    Sg = np.linspace(0, 2, 400001)
    lo, hi = Sg[:-1], Sg[1:]

    def Vcert(l0, l):
        return l0 + np.max(np.sqrt(hi + l * l * hi * hi) - (l0 + l) * lo + 0.75 * l * hi * hi)

    Sc = np.linspace(0, 2, 4001)

    def Vfast(l0, l):
        return l0 + np.max(np.sqrt(Sc + l * l * Sc * Sc) - (l0 + l) * Sc + 0.75 * l * Sc * Sc)

    best = (9, 0, 0)
    for l in np.linspace(0, 1.2, 121):
        for l0 in np.linspace(0.2, 1.2, 201):
            v = Vfast(l0, l)
            if v < best[0]:
                best = (v, l0, l)
    v, l0, l = best
    for step in [0.002, 0.0005, 0.0001]:
        cand = [(Vfast(l0 + a * step, l + b * step), l0 + a * step, l + b * step)
                for a in range(-10, 11) for b in range(-10, 11) if l + b * step >= 0]
        v, l0, l = min(cand)
    cert = Vcert(l0, l)
    cert0 = min(Vcert(m, 0.0) for m in np.linspace(0.3, 0.8, 501))
    print("dual (TV allowed):   lambda0=%.4f lambda=%.4f  certified B <= %.6f   R <= %.6f" % (l0, l, cert, (1 + cert) / 2))
    print("lambda=0 only (Jensen, B<=1): %.6f" % cert0)
    return cert


if __name__ == "__main__":
    ok1 = part1()
    ok2 = part2()
    c = part3()
    print("ALL CHECKS", "OK" if (ok1 and ok2) else "FAIL")
