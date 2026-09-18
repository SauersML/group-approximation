#!/usr/bin/env python3
"""Numerical check of the paired staggered transport model.

Model (claim toms-chern-swap-count-allows-depth-one-drops, proof route
toms-depth-one-drops-model-proof):
  base K = [0,1] x CP^j, line bundles L_1 = O(-2) (range of z(x)z/|z|^2 in C^((j+1)^2))
  and L_2 = O(-1) (range of z/|z| in C^(j+1)); c_1 = -2u and -u, distinct and nonzero.
  R coordinates, t_i = (i - 1/2)/R + eta, eta = 1/(8R), sigma(i) = R+1-i (1-based).
  a'(s) = sum_i g_i(s) e_ii,  g_i(s) = clip(R (s - t_i), 0, 1),  so rank a'(s) = #{i : t_i < s}.
  P(s) = a'(s) (x) gamma_1 + a'(1-s) (x) gamma_2, the slice form of a swap pushforward
  along Z = {(x(s), x(1-s))}.
  Q(s) = sum_i Q^(i)(s), where Q^(i) lives on the slots (i, L_2) and (sigma(i), L_1):
     Q^(i) = X X^* + rho_i gamma_1[(sigma(i), L_1)],
     X = cos(theta_i) gamma_2[(i, L_2)] + sin(theta_i) Sigma',  Sigma' = gamma_1 T^* gamma_2,
  a continuous section of Hom(L_2, L_1) vanishing exactly on {z_0 = 0}.
  Pair i transports in the window W_i = [c_i - eta, c_i + eta], c_i = 1 - (i - 1/2)/R:
  theta ramps on the first half of W_i, rho on the second half. The windows are disjoint.

Checked on a grid that includes every c_i:
  (a) Q - P >= 0, so P <~ Q;
  (b) rank Q in {R-1, R}: the drop depth is one;
  (c) rank Q = R-1 exactly at s = c_i on the hyperplane z_0 = 0, never off it;
  (d) |rank a'(s) - R s| <= 1, so the swap pushforward carries the leaf-average profile h = s;
  (e) rank P at s = 0 and s = 1 is R (the endpoint data of the transport bound).
A constant-rank target would need rank >= 2 max(R_x, R_y) = 2R
(toms-constant-rank-twisted-transport-costs-double-rank).
Run: nice -n 10 timeout 1200 python3 staggered_transport_model.py > results.json
"""
import json
import numpy as np

TOL = 1e-8


def run(j, R, seed):
    rng = np.random.default_rng(seed)
    n1, n2 = (j + 1) ** 2, j + 1
    blk = n1 + n2
    eta = 1.0 / (8 * R)
    T = np.kron(np.eye(j + 1)[0:1, :], np.eye(j + 1))  # u (x) w -> u_0 w, C^(n1) -> C^(n2)
    t = [(i + 0.5) / R + eta for i in range(R)]        # 0-based i
    c = [1 - (i + 0.5) / R for i in range(R)]
    sig = [R - 1 - i for i in range(R)]

    def gammas(z):
        z = z / np.linalg.norm(z)
        v = np.kron(z, z)
        return np.outer(v, v.conj()), np.outer(z, z.conj())

    def g(i, s):
        return float(np.clip(R * (s - t[i]), 0.0, 1.0))

    def schedule(i, s):
        a = c[i] - eta
        if s <= a:
            return 0.0, 0.0
        if s <= c[i]:
            return (np.pi / 2) * (s - a) / eta, 0.0
        if s <= c[i] + eta:
            return np.pi / 2, (s - c[i]) / eta
        return np.pi / 2, 1.0

    def fields(s, z):
        g1, g2 = gammas(z)
        Sp = g1 @ T.conj().T @ g2  # n1 x n2, section of Hom(L_2, L_1)
        N = R * blk
        P = np.zeros((N, N), complex)
        Q = np.zeros_like(P)
        for i in range(R):
            o = i * blk
            P[o:o + n1, o:o + n1] += g(i, s) * g1
            P[o + n1:o + blk, o + n1:o + blk] += g(i, 1 - s) * g2
        for i in range(R):
            th, rho = schedule(i, s)
            src = slice(i * blk + n1, i * blk + blk)        # slot (i, L_2)
            dst = slice(sig[i] * blk, sig[i] * blk + n1)    # slot (sigma(i), L_1)
            X = np.zeros((N, n2), complex)
            X[src, :] = np.cos(th) * g2
            X[dst, :] = np.sin(th) * Sp
            Q += X @ X.conj().T
            Q[dst, dst] += rho * g1
        return P, Q

    def rank(M):
        return int(np.sum(np.linalg.eigvalsh(M) > TOL))

    grid = sorted(set(list(np.linspace(0, 1, 241)) + c))
    pts_generic = [rng.normal(size=j + 1) + 1j * rng.normal(size=j + 1) for _ in range(5)]
    pts_hyper = []
    for _ in range(5):
        z = rng.normal(size=j + 1) + 1j * rng.normal(size=j + 1)
        z[0] = 0
        pts_hyper.append(z)

    min_gap, ranks, drops, profile_err = np.inf, set(), [], 0.0
    for s in grid:
        ra = sum(1 for i in range(R) if g(i, s) > 0)
        profile_err = max(profile_err, abs(ra - R * s))
        for tag, pts in (("generic", pts_generic), ("hyperplane", pts_hyper)):
            for z in pts:
                P, Q = fields(s, z)
                min_gap = min(min_gap, float(np.linalg.eigvalsh(Q - P).min()))
                rq = rank(Q)
                ranks.add(rq)
                if rq < R:
                    drops.append((round(s, 6), tag))
    drop_s = sorted({d[0] for d in drops})
    expected = sorted(round(x, 6) for x in c)
    out = {
        "j": j, "R": R,
        "min_eigenvalue_Q_minus_P": min_gap,
        "ranks_of_Q_seen": sorted(ranks),
        "drop_parameters": drop_s,
        "expected_drop_parameters": expected,
        "drops_off_hyperplane": sum(1 for d in drops if d[1] == "generic"),
        "max_abs_rank_aprime_minus_Rs": profile_err,
        "rank_P_at_s0": rank(fields(0.0, pts_generic[0])[0]),
        "rank_P_at_s1": rank(fields(1.0, pts_generic[0])[0]),
    }
    out["all_checks_pass"] = bool(
        min_gap > -1e-9 and out["ranks_of_Q_seen"] == [R - 1, R] and drop_s == expected
        and out["drops_off_hyperplane"] == 0 and profile_err <= 1.0
        and out["rank_P_at_s0"] == R and out["rank_P_at_s1"] == R)
    return out


if __name__ == "__main__":
    results = [run(2, 4, 20260917), run(3, 3, 20260918)]
    print(json.dumps({"cases": results,
                      "all_checks_pass": all(r["all_checks_pass"] for r in results)}, indent=2))
