#!/usr/bin/env python3
"""Exact check of the rank-locality inequalities on bin processes (order-2 chains on N bins, uniform jitter).

For a stationary process with atomless marginal, no ties, and V_t = F(X_t) uniform (rank coordinate):
  (R1)  int_0^e (1 - S) dV >= P(V_0 < e <= V_{-1})       for every e in [0,1],
  (R2)  E[(S - 1)(V - 1/2)] >= delta/2,   delta = E|V_1 - V_0|,
  (R3)  Var S >= 3 delta^2,
  (R4)  B <= Phi_3 <= E sqrt(S) <= 1 - Var(S)/(2 (1+sqrt2)^2) <= 1 - 3 delta^2/(2 (1+sqrt2)^2).
Inside bin k the level is m = bin k at jitter v in [0,1], so U(m) = sum_{j<k} r_k(j) + r_k(k) v and
V = Pi_{<k} + pi_k v; all expectations below are exact polynomial integrals in v.
Kernels tested: random order-2 kernels, and the saved Phi_3 optimisers best_K2_N*.pt.
"""
import glob
import os
import sys
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from three_point_bound import pair_stationary, phi_order2   # noqa: E402

torch.set_default_dtype(torch.float64)
C_SQ = 2 * (1 + 2 ** 0.5) ** 2


def stats(K2):
    N = K2.shape[0]
    Pi = pair_stationary(K2)                  # Pi[a,b] = P(X_{-1}=a, X_0=b) = P(X_0=a, X_1=b)
    p = Pi.sum(0)
    cum = torch.cat([torch.zeros(1), torch.cumsum(p, 0)[:-1]])   # Pi_{<k}
    # U = uA + uB v, D = dA + dB v at bin k
    rk = Pi / p[None, :]                      # rk[j,k] = P(X_{-1}=j | X_0=k)
    fk = Pi.T / p[None, :]                    # fk[j,k] = P(X_1=j | X_0=k)
    lower = torch.triu(torch.ones(N, N), 1)   # j<k
    a = ((rk + fk) * lower).sum(0)
    b = torch.diagonal(rk) + torch.diagonal(fk)
    # S - 1 = (a - 1) + b v ;  V - 1/2 = (cum - 1/2) + p v ;  E v = 1/2, E v^2 = 1/3
    s0, s1 = a - 1, b
    w0, w1 = cum - 0.5, p
    ES = (p * (s0 + s1 / 2)).sum()
    cov = (p * (s0 * w0 + (s0 * w1 + s1 * w0) / 2 + s1 * w1 / 3)).sum()
    varS = (p * (s0 * s0 + s0 * s1 + s1 * s1 / 3)).sum() - ES ** 2
    mid = cum + p / 2
    dmat = (mid[None, :] - mid[:, None]).abs()
    dmat = dmat - torch.diag(torch.diagonal(dmat)) + torch.diag(p / 3)
    delta = (Pi * dmat).sum()
    phi = phi_order2(K2)
    return dict(ES=ES.item(), cov=cov.item(), varS=varS.item(), delta=delta.item(), phi=phi.item())


def report(name, st):
    ok2 = st['cov'] >= st['delta'] / 2 - 1e-12
    ok3 = st['varS'] >= 3 * st['delta'] ** 2 - 1e-12
    bound = 1 - 3 * st['delta'] ** 2 / C_SQ
    ok4 = st['phi'] <= 1 - st['varS'] / C_SQ + 1e-12
    print("%-22s ES=%.6f delta=%.4f cov=%.5f>=%.5f %s  VarS=%.5f>=%.5f %s  Phi3=%.6f <= %.6f <= %.6f %s" % (
        name, st['ES'], st['delta'], st['cov'], st['delta'] / 2, ok2, st['varS'], 3 * st['delta'] ** 2, ok3,
        st['phi'], 1 - st['varS'] / C_SQ, bound, ok4))
    return ok2 and ok3 and ok4


if __name__ == "__main__":
    torch.manual_seed(7)
    allok = True
    for t in range(12):
        N = [3, 5, 8][t % 3]
        K2 = torch.softmax(torch.randn(N, N, N) * (0.5 + t / 3), 2)
        allok &= report("random N=%d #%d" % (N, t), stats(K2))
    for f in sorted(glob.glob(os.path.join(HERE, "best_K2_N*.pt"))):
        allok &= report(os.path.basename(f), stats(torch.load(f)))
    print("ALL OK" if allok else "FAILED")
