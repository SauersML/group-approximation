#!/usr/bin/env python3
"""Float scouting of the 1D size problem that the i.i.d. product-form forest ansatz reduces to.

Phi(nu, eta) = BC(nu, eta)^2 + BC(nu * eta, nu),   BC(p, q) = sum_m sqrt(p(m) q(m)),
nu, eta probability vectors on {1..M}; nu * eta is convolution (sizes >= 2; the part above M is
irrelevant because nu vanishes there).  The ansatz value is ||P|| >= Phi / 2.
nu = size law of the pointer tree, eta = size law of every other tree.
Usage: one_d_opt.py M [iters]
"""
import sys, json
import torch
torch.set_default_dtype(torch.float64)


def phi(a, b, M):
    nu = torch.softmax(a, 0)
    eta = torch.softmax(b, 0)
    L = 2 * M
    conv = torch.fft.irfft(torch.fft.rfft(nu, L) * torch.fft.rfft(eta, L), L)[:M - 1].clamp(min=0)
    # conv[k] = (nu*eta)(size k+2), k = 0..M-2 ; nu[1:] are sizes 2..M
    bc1 = torch.sum(torch.sqrt(nu * eta))
    bc2 = torch.sum(torch.sqrt(nu[1:] * conv + 1e-300))
    return bc1 ** 2 + bc2, nu, eta


def optimise(M, iters=20, init=None):
    x = torch.log(torch.arange(1, M + 1, dtype=torch.float64))
    if init is None:
        a, b = (-1.0 * x).clone(), (-1.0 * x).clone()
    else:
        a, b = init[0].clone(), init[1].clone()
    a.requires_grad_(); b.requires_grad_()
    opt = torch.optim.LBFGS([a, b], lr=1, max_iter=200, history_size=100,
                            line_search_fn='strong_wolfe', tolerance_grad=1e-12, tolerance_change=1e-15)
    for _ in range(iters):
        def closure():
            opt.zero_grad()
            v, _, _ = phi(a, b, M)
            (-v).backward()
            return -v
        opt.step(closure)
    v, nu, eta = phi(a, b, M)
    return v.item(), a.detach(), b.detach(), nu.detach(), eta.detach()


if __name__ == '__main__':
    Ms = [int(t) for t in sys.argv[1].split(',')]
    iters = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    for M in Ms:
        v, a, b, nu, eta = optimise(M, iters)
        s = torch.arange(1, M + 1, dtype=torch.float64)
        print(json.dumps({'M': M, 'Phi': round(v, 8), 'normP': round(v / 2, 8),
                          'mean_nu': round(float((nu * s).sum()), 3), 'mean_eta': round(float((eta * s).sum()), 3),
                          'nu1': round(float(nu[0]), 5), 'eta1': round(float(eta[0]), 5)}), flush=True)
