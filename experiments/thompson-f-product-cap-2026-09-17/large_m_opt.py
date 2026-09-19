#!/usr/bin/env python3
"""Float scouting of Phi(nu, eta) = BC(nu,eta)^2 + BC(nu*eta, nu) at large support M.

Low-dimensional parametrisation: with t = log(m)/log(M) in [0,1],
    log nu(m)  = -log m + A(t) + a_m [m <= S],    log eta(m) = -log m + B(t) + b_m [m <= S],
A, B piecewise linear on K knots, a, b free on the first S sizes.  Normalised by logsumexp.
Usage: large_m_opt.py M [K] [S] [iters] [out.pt] [init.pt]
"""
import sys, json, math
import torch
torch.set_default_dtype(torch.float64)


def interp(knots, t):
    K = knots.shape[0]
    x = t * (K - 1)
    i = torch.clamp(x.floor().long(), 0, K - 2)
    f = x - i
    return knots[i] * (1 - f) + knots[i + 1] * f


def build(p, M, S):
    m = torch.arange(1, M + 1, dtype=torch.float64)
    t = torch.log(m) / math.log(M)
    la = -torch.log(m) + interp(p['A'], t)
    lb = -torch.log(m) + interp(p['B'], t)
    la = torch.cat([la[:S] + p['a'], la[S:]])
    lb = torch.cat([lb[:S] + p['b'], lb[S:]])
    nu = torch.exp(la - torch.logsumexp(la, 0))
    eta = torch.exp(lb - torch.logsumexp(lb, 0))
    return nu, eta


def phi(nu, eta, M):
    L = 1 << (2 * M - 1).bit_length()
    conv = torch.fft.irfft(torch.fft.rfft(nu, L) * torch.fft.rfft(eta, L), L)[:M - 1].clamp(min=0)
    bc1 = torch.sum(torch.sqrt(nu * eta))
    bc2 = torch.sum(torch.sqrt(nu[1:] * conv + 1e-300))
    return bc1 ** 2 + bc2


def main():
    M = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    S = int(sys.argv[3]) if len(sys.argv) > 3 else 16
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 10
    out = sys.argv[5] if len(sys.argv) > 5 else None
    p = {'A': torch.zeros(K), 'B': torch.zeros(K), 'a': torch.zeros(S), 'b': torch.zeros(S)}
    if len(sys.argv) > 6:
        q = torch.load(sys.argv[6])
        for k in ('a', 'b'):
            p[k] = q[k].clone()
        for k in ('A', 'B'):  # resample knots
            old = q[k]
            p[k] = interp(old, torch.linspace(0, 1, K)).clone()
    params = [p[k].requires_grad_() for k in ('A', 'B', 'a', 'b')]
    opt = torch.optim.LBFGS(params, lr=1, max_iter=100, history_size=50, line_search_fn='strong_wolfe',
                            tolerance_grad=1e-12, tolerance_change=1e-15)
    for _ in range(iters):
        def closure():
            opt.zero_grad()
            v = phi(*build(p, M, S), M)
            (-v).backward()
            return -v
        opt.step(closure)
    with torch.no_grad():
        v = phi(*build(p, M, S), M).item()
    if out:
        torch.save({k: p[k].detach() for k in p}, out)
    print(json.dumps({'M': M, 'K': K, 'S': S, 'Phi': v, 'normP': v / 2}), flush=True)


if __name__ == '__main__':
    main()
