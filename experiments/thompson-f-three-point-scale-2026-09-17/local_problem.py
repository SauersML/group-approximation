#!/usr/bin/env python3
"""Translation-invariant ("rank-local") limit of the three-point projection bound Phi_3.

Global rigidity (see the research node) forces every stationary size process with B -> 1 to be rank-local:
E|F(X_1) - F(X_0)| -> 0.  Locally such a process is a walk on Z (bins of width 1, uniform jitter inside a
bin) whose increments t_j = X_j - X_{j-1} form a stationary chain with kernel K[t,u] = P(next increment u |
increment t), t,u in {-L..L}, stationary law g, pair law h[t,u] = g[t] K[t,u].  Per unit of level m (unit
bin mass), the bin formula of three_point_bound.py becomes

  c_L(d) = sum_t sqrt(h[t,d] g[t+d]),   c_R(d) = sum_w sqrt(h[-d,w] g[w-d]),   C(d) = c_L(d)^2 + c_R(d)^2,
  A = sum_{d>=1} C(d),  C0 = C(0),  Psi = (2/(3 C0)) ((A + C0)^{3/2} - A^{3/2}).

Cauchy-Schwarz gives Psi <= 1.  Modes:
  check        : Psi agrees with the global bin formula on a long reflected strip (N bins) as N grows.
  opt L...     : maximise Psi over increment kernels on {-L..L}.
"""
import sys
import os
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'thompson-f-markov-forest-2026-09-17'))
from markov_ansatz import stationary          # noqa: E402
from three_point_bound import phi_from_P3      # noqa: E402

torch.set_default_dtype(torch.float64)


def psi(K):
    n = K.shape[0]
    L = (n - 1) // 2
    g = stationary(K)
    h = g[:, None] * K
    gp = torch.cat([g, torch.zeros(n)])        # g at index t+L, zero outside [-L, L]

    def G(x):                                  # x: tensor of integer increments
        idx = x + L
        ok = (idx >= 0) & (idx < n)
        return torch.where(ok, gp[idx.clamp(0, 2 * n - 1)], torch.zeros(()))

    t = torch.arange(-L, L + 1)
    C = []
    for d in range(0, L + 1):
        cl = torch.sqrt((h[:, d + L] * G(t + d)).clamp_min(0)).sum()
        cr = torch.sqrt((h[-d + L, :] * G(t - d)).clamp_min(0)).sum()
        C.append(cl ** 2 + cr ** 2)
    C = torch.stack(C)
    C0 = C[0].clamp_min(1e-300)
    A = C[1:].sum()
    return (2.0 / 3.0) * ((A + C0) ** 1.5 - A ** 1.5) / C0


def strip_P3(K, N):
    """Order-2 bin chain on {0..N-1} whose increments follow K, reflected at the ends (reverse the
    increment), with its stationary 3-point law.  For large N the per-bin value tends to psi(K)."""
    n = K.shape[0]
    L = (n - 1) // 2
    # state (x, t): position x, last increment t
    S = N * n
    T = torch.zeros(S, S)
    for x in range(N):
        for ti in range(n):
            for ui in range(n):
                u = ui - L
                y = x + u
                uj = ui
                if y < 0 or y >= N:
                    y = x - u
                    uj = 2 * L - ui
                    if y < 0 or y >= N:
                        y, uj = x, L
                T[x * n + ti, y * n + uj] += K[ti, ui]
    pi = stationary(T).reshape(N, n)
    P3 = torch.zeros(N, N, N)
    for x in range(N):
        for ti in range(n):
            a = x - (ti - L)
            if a < 0 or a >= N:
                continue
            for y in range(N):
                ui = (y - x) + L
                if 0 <= ui < n:
                    P3[a, x, y] += pi[x, ti] * T[x * n + ti, y * n + ui]
    return P3


def check():
    torch.manual_seed(3)
    # mirror-symmetric (drift-free) kernel: the reflected strip is locally uniform, so Phi_3 -> psi (O(1/N)).
    # (A kernel with drift piles up at one end of the strip and the strip then does not realise psi.)
    L = 2
    K = torch.softmax(torch.randn(2 * L + 1, 2 * L + 1), 1)
    K = (K + K.flip(0).flip(1)) / 2
    print("check: psi(K) = %.6f" % psi(K).item())
    for N in [20, 40, 80]:
        v = phi_from_P3(strip_P3(K, N)).item()
        print("check: strip N=%d  Phi_3 = %.6f" % (N, v), flush=True)
    # iid increments uniform on {-L..L}: random walk
    K = torch.full((2 * L + 1, 2 * L + 1), 1.0 / (2 * L + 1))
    print("check: iid uniform increments psi = %.6f" % psi(K).item())


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
        # opt: any increment chain; optsym: mirror-symmetric chains K[t,u] = K[-t,-u] (drift-free, and
        # realised by reflected strips, so their values are lower bounds for sup Phi_3 as N -> infinity)
        sym = sys.argv[1] == "optsym"

        def kern(z):
            if sym:
                z = (z + z.flip(0).flip(1)) / 2
            return torch.softmax(z, 1)
        for L in [int(a) for a in sys.argv[2:]]:
            torch.manual_seed(L)
            n = 2 * L + 1
            best = -1.0
            for s in range(3):
                x0 = (0.3 + 0.7 * s) * torch.randn(n, n)
                v, x = lbfgs(lambda z: psi(kern(z)), x0, 2000)
                print("%s L=%d start %d  Psi=%.6f" % (sys.argv[1], L, s, v), flush=True)
                if v > best:
                    best = v
                    torch.save(kern(x), os.path.join(HERE, "best_local_%s_L%d.pt" % (sys.argv[1], L)))
            print("%s L=%d best Psi=%.6f" % (sys.argv[1], L, best), flush=True)
