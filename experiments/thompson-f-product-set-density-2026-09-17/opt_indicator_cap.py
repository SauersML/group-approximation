#!/usr/bin/env python3
"""Float scout (not used by any proof): maximize the indicator-set functional

    Psi(nu, eta, u) = S(u)^2 + M(nu, eta),
    S(u) = sum_s min(u eta_s, nu_s / u),     M = sum_m min(nu_m, (nu*eta)_m),

over probability vectors nu, eta on {1..N} and u > 0.  2*Psi bounds the limiting density
(average degree) of product-form indicator window sets; see the claim
thompson-f-product-forest-sets-have-density-at-most-3-5.

Usage: opt_indicator_cap.py N [restarts] [steps]
"""
import sys
import torch

torch.set_default_dtype(torch.float64)


def psi(a, b, lu):
    nu = torch.softmax(a, 0)
    eta = torch.softmax(b, 0)
    u = torch.exp(lu)
    N = nu.shape[0]
    # index 0 <-> size 1
    conv = torch.zeros(N)
    full = torch.nn.functional.conv1d(nu.view(1, 1, -1), eta.flip(0).view(1, 1, -1), padding=N - 1).view(-1)
    # full[k] = sum_{i+j=k} nu_i eta_j with i,j 0-based, i.e. size (i+1)+(j+1) = k+2 -> 0-based index k+1
    conv[1:] = full[: N - 1]
    S = torch.minimum(u * eta, nu / u).sum()
    M = torch.minimum(nu, conv).sum()
    return S * S + M, S, M


def run(N, restarts=40, steps=4000, seed=0):
    g = torch.Generator().manual_seed(seed)
    best = (-1, None)
    for r in range(restarts):
        a = (torch.randn(N, generator=g) * 2).requires_grad_()
        b = (torch.randn(N, generator=g) * 2).requires_grad_()
        lu = torch.zeros(1).requires_grad_()
        opt = torch.optim.Adam([a, b, lu], lr=0.05)
        for t in range(steps):
            opt.zero_grad()
            val, _, _ = psi(a, b, lu[0])
            (-val).backward()
            opt.step()
            if t == steps // 2:
                for pg in opt.param_groups:
                    pg['lr'] = 0.01
        with torch.no_grad():
            val, S, M = psi(a, b, lu[0])
        if val.item() > best[0]:
            best = (val.item(), (torch.softmax(a, 0).detach(), torch.softmax(b, 0).detach(),
                                 torch.exp(lu).item(), S.item(), M.item()))
    return best


if __name__ == '__main__':
    N = int(sys.argv[1])
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    T = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    val, (nu, eta, u, S, M) = run(N, R, T)
    print('N=%d  Psi=%.6f  density bound 2Psi=%.6f  S=%.5f  M=%.5f  u=%.4f' % (N, val, 2 * val, S, M, u))
    print('nu :', ' '.join('%.3f' % x for x in nu.tolist()))
    print('eta:', ' '.join('%.3f' % x for x in eta.tolist()))
