#!/usr/bin/env python3
"""Continuum (scale -> infinity) limit of the 1D size problem, heuristic.

In log-size coordinates with huge spread, X + Y ~ max(X, Y).  Put u = H(x) (cdf of nu) and
phi(u) = K(H^{-1}(u)) (cdf of eta).  Then
    BC(nu, eta)       -> int_0^1 sqrt(phi'(u)) du,
    BC(nu, nu * eta)  -> int_0^1 sqrt((u phi(u))') du,
and J(phi) = (int sqrt(phi'))^2 + int sqrt((u phi)') over nondecreasing phi, 0 <= phi <= 1.
Discretised on a grid of n cells; phi(0) = c0 >= 0 (mass of eta below nu), increments psi_i >= 0.
Usage: continuum_opt.py n
"""
import sys, json
import torch
torch.set_default_dtype(torch.float64)

n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
u = torch.linspace(0, 1, n + 1)
du = 1.0 / n


def J(z):
    # z[0] -> c0 share, z[1:] -> increments, z[-1] -> mass of eta above nu ; softmax keeps the total 1
    w = torch.softmax(z, 0)
    c0, psi = w[0], w[1:n + 1]
    phi = c0 + torch.cat([torch.zeros(1), torch.cumsum(psi, 0)])
    up = u * phi
    d = up[1:] - up[:-1]
    bc1 = torch.sum(torch.sqrt(psi * du))
    bc2 = torch.sum(torch.sqrt(d.clamp(min=0) * du + 1e-300))
    return bc1 ** 2 + bc2, phi


z = torch.zeros(n + 2)
z[0] = -3.0
z.requires_grad_()
opt = torch.optim.LBFGS([z], lr=1, max_iter=500, history_size=100, line_search_fn='strong_wolfe',
                        tolerance_grad=1e-13, tolerance_change=1e-16)
for _ in range(30):
    def closure():
        opt.zero_grad()
        v, _ = J(z)
        (-v).backward()
        return -v
    opt.step(closure)
v, phi = J(z)
print(json.dumps({'n': n, 'J': v.item(), 'normP': v.item() / 2, 'phi0': phi[0].item(), 'phi1': phi[-1].item(),
                  'phi_at': {str(t): phi[int(t * n)].item() for t in (0.1, 0.25, 0.5, 0.75, 0.9)}}))
