#!/usr/bin/env python3
"""Four-point projection bound Phi_4 >= B for size-only test vectors of F in the log-scale limit (E2).

Same setting as three_point_bound.py, but both neighbours of the merged pair are kept.  Projecting the
merged image and the target onto (side, s, m, left neighbour a, right neighbour b):

  left child small  (a, s, m, b) = (X_{-1}, X_0, X_1, X_2),  s < m;
  right child small (a, m, s, b) = (X_{-1}, X_0, X_1, X_2),  s < m;
  target            (a, m, b)    = (X_{-1}, X_0, X_1) with split (side, s) ~ kappa(.|m).

  c_L(s,m) = int int sqrt(p4(a,s,m,b) p3(a,m,b)) da db,  c_R(s,m) = int int sqrt(p4(a,m,s,b) p3(a,m,b)),
  Phi_4 = int dm sqrt( int_{s<m} (c_L^2 + c_R^2) ds )   (kappa optimised),   B <= Phi_4 <= Phi_3.

Every stationary 4-point law is the 4-marginal of an order-3 chain; P4 is piecewise constant on N bins.
Modes: check (lossless on order-1 and order-2 chains: Phi_4 == scale_B2), opt N...
"""
import sys
import os
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'thompson-f-markov-forest-2026-09-17'))
from markov_ansatz import stationary          # noqa: E402
from scale_limit_order2 import scale_B2       # noqa: E402
from three_point_bound import phi_order2       # noqa: E402

torch.set_default_dtype(torch.float64)


def triple_stationary(K3):
    """K3[a,b,c,d] = P(X_2=d | X_{-1}=a, X_0=b, X_1=c); stationary law of the triple chain."""
    N = K3.shape[0]
    T = torch.zeros(N, N, N, N, N, N)
    i = torch.arange(N)
    # (a,b,c) -> (b,c,d)
    T[:, i[:, None], i[None, :], i[:, None], i[None, :], :] = K3
    return stationary(T.reshape(N ** 3, N ** 3)).reshape(N, N, N)


def phi_from_P4(P4):
    N = P4.shape[0]
    P3 = P4.sum(3)                                    # P3[a,m,b] = law of (X_{-1},X_0,X_1)
    # c_L[s,m] = sum_{a,b} sqrt(P4[a,s,m,b] P3[a,m,b])
    cL = torch.sqrt((P4 * P3.unsqueeze(1)).clamp_min(0)).sum((0, 3))
    # c_R[s,m] = sum_{a,b} sqrt(P4[a,m,s,b] P3[a,m,b])
    cR = torch.sqrt((P4 * P3.unsqueeze(2)).clamp_min(0)).sum((0, 3)).T
    C = cL ** 2 + cR ** 2
    low = torch.triu(torch.ones(N, N), diagonal=1)
    A = (C * low).sum(0)
    d = torch.diagonal(C).clamp_min(1e-300)
    return ((2.0 / 3.0) * ((A + d) ** 1.5 - A ** 1.5) / d).sum()


def phi_order3(K3):
    Pi = triple_stationary(K3)
    return phi_from_P4(Pi.unsqueeze(3) * K3)


def check():
    torch.manual_seed(2)
    worst, gap = 0.0, 1.0
    for N in [2, 3, 4, 5]:
        for t in range(4):
            K = torch.softmax(torch.randn(N, N) * (1 + t), 1)
            K3 = K.expand(N, N, N, N).clone()
            K2 = K.expand(N, N, N).clone()
            worst = max(worst, abs(phi_order3(K3).item() - scale_B2(K2).item()))
            K2 = torch.softmax(torch.randn(N, N, N) * (1 + t), 2)
            K3 = K2.unsqueeze(0).expand(N, N, N, N).clone()
            gap = min(gap, phi_order3(K3).item() - scale_B2(K2).item())
    print("check: max |Phi_4 - B| over 16 order-1 kernels (lossless) = %.2e" % worst)
    print("check: min (Phi_4 - B) over 16 order-2 kernels = %.2e (must be >= 0)" % gap)
    mono = 0.0
    for t in range(20):
        N = 4
        K3 = torch.softmax(torch.randn(N, N, N, N) * 2, 3)
        Pi = triple_stationary(K3)
        P4 = Pi.unsqueeze(3) * K3
        P3 = P4.sum(3)
        K2 = P3 / P3.sum(2, keepdim=True)            # order-2 chain with the same 3-point law
        mono = max(mono, phi_order3(K3).item() - phi_order2(K2).item())
    print("check: max (Phi_4 - Phi_3) on 20 random order-3 kernels = %.2e (must be <= 0)" % mono)


def lbfgs(f, x, iters):
    x = x.clone().requires_grad_(True)
    o = torch.optim.LBFGS([x], max_iter=iters, line_search_fn='strong_wolfe', tolerance_grad=1e-11,
                          tolerance_change=1e-13, history_size=50)

    def closure():
        o.zero_grad()
        v = -f(x)
        v.backward()
        return v
    o.step(closure)
    return f(x).item(), x.detach()


if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] == "check":
        check()
    else:
        for N in [int(a) for a in sys.argv[2:]]:
            torch.manual_seed(N)
            best = -1.0
            for t in range(3):
                x0 = (0.3 + 0.7 * t) * torch.randn(N, N, N, N)
                v, x = lbfgs(lambda z: phi_order3(torch.softmax(z, 3)), x0, 2000)
                K3 = torch.softmax(x, 3)
                print("N=%d start %d  Phi_4=%.6f" % (N, t, v), flush=True)
                if v > best:
                    best = v
                    torch.save(K3, os.path.join(HERE, "best_K3_N%d.pt" % N))
            print("N=%d best Phi_4=%.6f" % (N, best), flush=True)
