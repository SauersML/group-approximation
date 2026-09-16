"""Tests of Lemmas C, J, Rt(b), Corollary Rt, and Rt(a) on the graph zoo.
Usage: python3 tests.py seed
"""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog, minimize
from graphs import zoo


def T1_lemmaC(G, rng, trials=300):
    """p in |X| iff (*) (no charged empty quadrant)."""
    bad = 0
    nin = nout = 0
    for _ in range(trials):
        mode = rng.random()
        if mode < 0.4:
            p = G.random_point_X(rng)
        else:
            p = G.random_point_X(rng, dyadic=rng.choice([2, 4]))
            # perturb some coordinates
            for h in rng.sample(range(G.m), rng.randint(1, min(3, G.m))):
                p[h] = rng.choice([0.0, 1.0, rng.random(), 0.5])
        a = G.in_X(p)
        b = G.star(p) <= 1e-12
        nin += a
        nout += (not a)
        if a != b:
            bad += 1
    return dict(C_bad=bad, C_in=nin, C_out=nout)


def T2_lemmaJ(G, rng, trials=8):
    """Every minimizer of Phi over D has no charged empty quadrant; J feasible."""
    worst = 0.0
    worstJ = -np.inf
    rows = [G.Lcoef(x) for x in range(G.n)]
    A = np.array([r[0] for r in rows])
    const = np.array([r[1] for r in rows])
    for _ in range(trials):
        supp = rng.sample(range(G.n), rng.randint(1, min(G.n, 5)))
        mu = np.zeros(G.n)
        for s in supp:
            mu[s] = rng.random() + 0.01
        mu /= mu.sum()
        w = G.C.T @ mu  # w_h = mu(h^1)
        Lw = A @ w + const
        integ = G.D @ mu
        assert np.allclose(Lw, integ), "(2.1) fails"
        obj = A.sum(axis=0)
        res = linprog(obj, A_ub=A, b_ub=Lw - const, bounds=[(0, 1)] * G.m, method="highs")
        phistar = res.fun
        # over the optimal face, maximize min(q_A,q_B) for each empty quadrant
        for (h, a, g, b) in G.Q:
            # variables c (m) and t; maximize t
            # t <= q_A(c): if a==1, q=c_h -> t - c_h <= 0 ; else q=1-c_h -> t + c_h <= 1
            r1 = np.zeros(G.m + 1); r1[-1] = 1
            r2 = np.zeros(G.m + 1); r2[-1] = 1
            if a == 1:
                r1[h] = -1; b1 = 0.0
            else:
                r1[h] = 1; b1 = 1.0
            if b == 1:
                r2[g] = -1; b2 = 0.0
            else:
                r2[g] = 1; b2 = 1.0
            Aub = np.vstack([np.hstack([A, np.zeros((G.n, 1))]),
                             np.hstack([obj, [0.0]])[None, :], r1[None, :], r2[None, :]])
            bub = np.concatenate([Lw - const, [phistar + 1e-9], [b1, b2]])
            cvec = np.zeros(G.m + 1); cvec[-1] = -1
            res2 = linprog(cvec, A_ub=Aub, b_ub=bub, bounds=[(0, 1)] * G.m + [(0, 1)], method="highs")
            worst = max(worst, -res2.fun)
        # direct J feasibility over |X|: min over X of max_x (L_x - L_x(w))
        val, _ = G.lp_minmax_X(list(range(G.n)), list(Lw))
        worstJ = max(worstJ, val)
    return dict(J_optface_charge=worst, J_X_minmax=worstJ)


def T3_Rtb(G, rng, trials=10):
    """D_p = {p} for p in |X|."""
    rows = [G.Lcoef(x) for x in range(G.n)]
    A = np.array([r[0] for r in rows])
    worst = 0.0
    for _ in range(trials):
        p = G.random_point_X(rng)
        bub = A @ p + 1e-12
        for h in range(G.m):
            for sgn in (1, -1):
                cvec = np.zeros(G.m); cvec[h] = -sgn
                res = linprog(cvec, A_ub=A, b_ub=bub, bounds=[(0, 1)] * G.m, method="highs")
                worst = max(worst, abs(res.x[h] - p[h]))
    return dict(Rtb_dev=worst)


def T4_CorRt(G, rng, trials=15):
    """min over box of max_i(L_{z_i}-rho_i) == min over |X|."""
    worst = 0.0
    for _ in range(trials):
        cn = rng.randint(2, min(G.n, 6))
        Z = rng.sample(range(G.n), cn)
        rho = [rng.uniform(0, G.D.max()) for _ in Z]
        vb, _ = G.lp_minmax_box(Z, rho)
        vx, _ = G.lp_minmax_X(Z, rho)
        worst = max(worst, abs(vb - vx))
    return dict(CorRt_mismatch=worst)


def T6_Rta(G, rng, trials=4):
    """r(c) = argmin_{D_c} Psi lies in |X| (numerical, SLSQP)."""
    rows = [G.Lcoef(x) for x in range(G.n)]
    A = np.array([r[0] for r in rows])
    obj = A.sum(axis=0)
    worst = 0.0
    for _ in range(trials):
        c = np.array([rng.random() for _ in range(G.m)])
        bub = A @ c
        cons = [{"type": "ineq", "fun": lambda y, bub=bub: bub - A @ y, "jac": lambda y: -A}]
        f = lambda y: obj @ y + (1 / 8) * (y @ y)
        jac = lambda y: obj + (1 / 4) * y
        res = minimize(f, c, jac=jac, constraints=cons, bounds=[(0, 1)] * G.m, method="SLSQP",
                       options=dict(ftol=1e-12, maxiter=500))
        worst = max(worst, G.star(res.x))
    return dict(Rta_star=worst)


if __name__ == "__main__":
    seed = int(sys.argv[1])
    rng = random.Random(seed)
    for G in zoo(seed):
        out = dict(name=G.name, n=G.n, m=G.m, k=G.k, median=G.median_ok, ham=G.hamming_ok)
        out.update(T1_lemmaC(G, rng))
        out.update(T2_lemmaJ(G, rng))
        out.update(T3_Rtb(G, rng))
        out.update(T4_CorRt(G, rng))
        out.update(T6_Rta(G, rng))
        print(out, flush=True)
