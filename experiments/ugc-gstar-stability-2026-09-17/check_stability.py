"""Numerical sanity check of Theorem S (gstar-star-linearity-is-stable-near-full-value).

GStar_n: F labels every (l-1)-space W and every l-space T of F_2^n by a linear functional
(stored as a representative vector g, F(S)(x) = <g,x> for x in S).
  val   = Pr_{W,u}[u notin W, F(W+u)|_W = F(W)]
  eps_W = Pr_{T > W}[F(T)|_W != F(W)],  eps = E_W eps_W
  Dmin_W = min_{psi | psi|_W = F(W)} Pr_u[sat(W,W+u), F(W+u)(u) != psi(u)]
  t_W   = Pr_{R > W, dim R = l+1}[the 3 edges W<T<R are sat and the 3 labels F(T) have
          no common linear extension to R]
Checks, on perturbed honest labellings and on two-functional mixtures:
  (F7)  per (l+1)-space R: #twisted stars in R <= 4/3 #unsat edges in R
  (BLR) Dmin_W <= t_W + 1.5 eps_W for every W
  (S)   t <= 4 eps,  eps <= 1 - val,  Dmin <= 5.5 (1 - val)
Also prints lambda_2/theta_0 of the Grassmann graph on (l-1)-spaces (numpy, if present)
against the closed form theta_1/theta_0 (BCN Thm 9.3.3) used by Theorem G.
Usage: python3 check_stability.py [trials]
"""
import itertools
import random
import sys


def dot(a, b):
    return bin(a & b).count("1") & 1


def subspaces(n, d):
    out = set()
    for basis in itertools.combinations(range(1, 1 << n), d):
        span = {0}
        for b in basis:
            span |= {s ^ b for s in span}
        if len(span) == 1 << d:
            out.add(frozenset(span))
    return sorted(out, key=sorted)


def agree(g, h, S):
    return all(dot(g, x) == dot(h, x) for x in S)


def analyse(n, l, FW, FT, Ws, Ts, Rs, Tidx):
    N = 1 << n
    tol = 1e-12
    val = eps = Dmin = t = 0.0
    sat = {}
    for W in Ws:
        for T in Ts:
            if W <= T:
                sat[W, T] = agree(FW[W], FT[T], W)
    for W in Ws:
        up = [T for T in Ts if W <= T]
        eW = sum(not sat[W, T] for T in up) / len(up)
        vW = sum(u not in W and sat[W, Tidx[W | {x ^ u for x in W}]] for u in range(N)) / N
        best = 1.0
        for psi in range(N):
            if not agree(psi, FW[W], W):
                continue
            bad = 0
            for u in range(N):
                if u in W:
                    continue
                T = Tidx[W | {x ^ u for x in W}]
                if sat[W, T] and dot(FT[T], u) != dot(psi, u):
                    bad += 1
            best = min(best, bad / N)
        ups = [R for R in Rs if W <= R]
        tw = 0
        for R in ups:
            ts = [T for T in up if T <= R]
            assert len(ts) == 3
            if all(sat[W, T] for T in ts):
                if not any(all(agree(g, FT[T], T) for T in ts) for g in range(N)):
                    tw += 1
        tW = tw / len(ups)
        assert best <= tW + 1.5 * eW + tol, ("BLR", best, tW, eW)
        val += vW
        eps += eW
        Dmin += best
        t += tW
    k = len(Ws)
    val, eps, Dmin, t = val / k, eps / k, Dmin / k, t / k
    for R in Rs:
        wr = [W for W in Ws if W <= R]
        tr = [T for T in Ts if T <= R]
        un = sum(not sat[W, T] for W in wr for T in tr if W <= T)
        tw = 0
        for W in wr:
            ts = [T for T in tr if W <= T]
            if all(sat[W, T] for T in ts) and not any(
                    all(agree(g, FT[T], T) for T in ts) for g in range(N)):
                tw += 1
        assert 3 * tw <= 4 * un, ("F7", tw, un)
    assert t <= 4 * eps + tol, ("t", t, eps)
    assert eps <= 1 - val + tol, ("eps", eps, val)
    assert Dmin <= 5.5 * (1 - val) + tol, ("S", Dmin, val)
    return val, eps, Dmin, t


def grassmann_ratio(n, d):
    Ws = subspaces(n, d)
    q = 2
    br = lambda k: (q ** k - 1) // (q - 1)
    th = lambda j: q ** (j + 1) * br(d - j) * br(n - d - j) - br(j)
    closed = th(1) / th(0)
    try:
        import numpy as np
    except ImportError:
        return closed, None
    A = np.array([[1.0 if len(a & b) == 1 << (d - 1) else 0.0 for b in Ws] for a in Ws])
    ev = sorted(np.linalg.eigvalsh(A))
    return closed, ev[-2] / ev[-1]


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rng = random.Random(20260917)
    for n, l in [(4, 2), (5, 2), (5, 3), (4, 3)]:
        Ws, Ts, Rs = subspaces(n, l - 1), subspaces(n, l), subspaces(n, l + 1)
        Tidx = {T: T for T in Ts}
        N = 1 << n
        closed, num = grassmann_ratio(n, l - 1)
        print(f"n={n} l={l}: Grassmann theta1/theta0 closed={closed:.4f} numeric={num}")
        assert closed < 0.5 and (num is None or abs(num - closed) < 1e-9)
        for p in [0.0, 0.02, 0.05, 0.1, 0.2, 0.4]:
            for mode in ["perturb", "mix"]:
                for _ in range(trials):
                    g0, g1 = rng.randrange(N), rng.randrange(N)
                    if mode == "perturb":
                        FW = {W: g0 if rng.random() > p else rng.randrange(N) for W in Ws}
                        FT = {T: g0 if rng.random() > p else rng.randrange(N) for T in Ts}
                    else:
                        FT = {T: g0 if rng.random() > p else g1 for T in Ts}
                        FW = {W: g0 if rng.random() > p else g1 for W in Ws}
                    val, eps, Dmin, t = analyse(n, l, FW, FT, Ws, Ts, Rs, Tidx)
                print(f"  {mode:7s} p={p:.2f} val={val:.4f} eps={eps:.4f} "
                      f"Dmin={Dmin:.4f} t={t:.4f} 5.5(1-val)={5.5 * (1 - val):.4f}")
    print("all checks passed")


if __name__ == "__main__":
    main()
