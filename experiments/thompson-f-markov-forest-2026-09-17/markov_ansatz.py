#!/usr/bin/env python3
"""Float scout: stationary Markov size chains as infinite-volume test vectors for Kesten's norm of F.

Model (pointed forest, pointer at 0): trees ..., T_-1, T_0, T_1, ...; x0 moves the pointer, x1 merges
T_0, T_1 into (T_0, T_1).  Test law Q: the sizes n_j form a stationary Markov chain (kernel K on
{1..M}, stationary law pi); given sizes, trees are independent with the recursive shape law
w(T) = kappa(|L| | |T|) w(L) w(R).  With u = sqrt(Q) the Rayleigh quotient is (BC_shift + BC_merge)/2,
BC_shift = 1 (stationarity), and

  BC_merge = sum_m sqrt( sum_k beta_k(m)^2 )           (kappa optimised, kappa(k|m) ~ beta_k(m)^2)
  beta_k(m) = G(k,m) * S(k,m-k) * H(m-k,m),
  S = sqrt(K), G = S^T diag(pi) S, H = S S^T  (H(i,j) = BC of rows i, j of K).

Product case K(a,.) = p gives BC_merge = BC(p, p*p).  Output: the best stationary Markov value and the
best product value at the same M.
"""
import sys
import torch

torch.set_default_dtype(torch.float64)


def stationary(K):
    M = K.shape[0]
    A = K.T - torch.eye(M)
    A = torch.cat([A[:-1], torch.ones(1, M)], 0)
    b = torch.zeros(M)
    b[-1] = 1.0
    return torch.linalg.solve(A, b)


def merge_bc(K, pi=None):
    M = K.shape[0]
    if pi is None:
        pi = stationary(K)
    S = torch.sqrt(K.clamp_min(0))
    G = S.T @ (pi.unsqueeze(1) * S)          # G[k,m] = sum_a pi(a) S(a,k) S(a,m)
    H = S @ S.T                               # H[i,j]
    # beta[k,m] for sizes k+1, m+1 (0-based index), need j = m-k >= 1
    idx = torch.arange(M)
    kk, mm = torch.meshgrid(idx, idx, indexing='ij')
    jj = mm - kk - 1                          # size(m) - size(k) = size(j): (m+1)-(k+1) = j+1
    valid = (jj >= 0)
    jc = jj.clamp_min(0)
    beta = G * S[kk, jc] * H[jc, mm]
    beta = torch.where(valid, beta, torch.zeros_like(beta))
    return torch.sqrt((beta ** 2).sum(0) + 1e-300).sum()


def product_bc(p):
    M = p.shape[0]
    conv = torch.zeros(M)
    for m in range(1, M):  # size m+1 = (k+1)+(j+1)
        conv[m] = (p[:m] * p[:m].flip(0)).sum()
    return torch.sqrt(p[1:] * conv[1:]).sum()


def opt(f, x, iters=400):
    x = x.clone().requires_grad_(True)
    o = torch.optim.LBFGS([x], max_iter=iters, line_search_fn='strong_wolfe', tolerance_grad=1e-12,
                          tolerance_change=1e-14, history_size=50)

    def closure():
        o.zero_grad()
        v = -f(x)
        v.backward()
        return v
    o.step(closure)
    return f(x).item(), x.detach()


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    torch.manual_seed(0)
    n = torch.arange(1, M + 1, dtype=torch.float64)
    # product: harmonic-ish start
    lp0 = -torch.log(n)
    vp, lp = opt(lambda z: product_bc(torch.softmax(z, 0)), lp0)
    print("M=%d product BC(p,p*p) = %.6f   R=(1+B)/2 = %.6f" % (M, vp, (1 + vp) / 2), flush=True)
    # markov: start at product optimum plus noise
    best = None
    for trial in range(3):
        L0 = lp.unsqueeze(0).repeat(M, 1) + 0.3 * trial * torch.randn(M, M)
        vm, L = opt(lambda z: merge_bc(torch.softmax(z, 1)), L0, iters=1500)
        print("  trial %d markov BC_merge = %.6f  R = %.6f" % (trial, vm, (1 + vm) / 2), flush=True)
        if best is None or vm > best[0]:
            best = (vm, L)
    torch.save({'M': M, 'logitsK': best[1], 'value': best[0], 'prod': vp, 'logp': lp},
               'markov_M%d.pt' % M)
