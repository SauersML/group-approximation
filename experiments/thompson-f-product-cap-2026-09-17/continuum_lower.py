#!/usr/bin/env python3
"""Float optimiser of the continuum functional J(h, k) (float scouting only).

h, k: positive probability vectors on n log-scale cells, H, K their cdfs (H_0 = K_0 = 0).
    J = (sum_i sqrt(h_i k_i))^2 + sum_i I_i,   I_i = int_0^1 sqrt(a_i + b_i s) ds
      = (2/3)(x + sqrt(x y) + y) / (sqrt x + sqrt y),  x = a_i + b_i, y = a_i,
    a_i = h_i (h_i K_{i-1} + k_i H_{i-1}),  b_i = 2 h_i^2 k_i,
so sum_i I_i = int_0^1 sqrt(h(t) (h(t) K(t) + k(t) H(t))) dt for the step densities
h(t) = n h_i on cell i.  EXACT = False uses the trapezoid lower bound (sqrt x + sqrt y)/2 instead.
Usage: continuum_lower.py n [out.json]   (writes h, k as floats)
"""
import sys, json
import torch
torch.set_default_dtype(torch.float64)


def jlo(zh, zk):
    h = torch.softmax(zh, 0); k = torch.softmax(zk, 0)
    H = torch.cat([torch.zeros(1), torch.cumsum(h, 0)[:-1]])
    K = torch.cat([torch.zeros(1), torch.cumsum(k, 0)[:-1]])
    a = h * (h * K + k * H)
    b = 2 * h * h * k
    bc1 = torch.sum(torch.sqrt(h * k))
    x = (a + b).clamp(min=1e-250); y = a.clamp(min=0)
    sx = torch.sqrt(x); sy = torch.cat([torch.zeros(1), torch.sqrt(y[1:].clamp(min=1e-250))])
    if EXACT:  # int_0^1 sqrt(y + (x-y) s) ds = (2/3)(x + sqrt(xy) + y)/(sqrt x + sqrt y)
        t2 = torch.sum((2.0 / 3.0) * (x + sx * sy + y) / (sx + sy))
    else:
        t2 = torch.sum(sx + sy) / 2
    return bc1 ** 2 + t2


EXACT = True


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    zh = torch.zeros(n, requires_grad=True)
    zk = torch.zeros(n)
    with torch.no_grad():
        zk[0] = 2.0
    zk.requires_grad_()
    opt = torch.optim.LBFGS([zh, zk], lr=1, max_iter=500, history_size=100, line_search_fn='strong_wolfe',
                            tolerance_grad=1e-13, tolerance_change=1e-16)
    for _ in range(40):
        def closure():
            opt.zero_grad()
            v = jlo(zh, zk)
            (-v).backward()
            return -v
        opt.step(closure)
    v = jlo(zh, zk).item()
    h = torch.softmax(zh, 0).detach(); k = torch.softmax(zk, 0).detach()
    print(json.dumps({'n': n, 'J_lo': v, 'normP_lo': v / 2, 'k1': k[0].item(), 'h1': h[0].item()}), flush=True)
    if len(sys.argv) > 2:
        with open(sys.argv[2], 'w') as fh:
            json.dump({'n': n, 'h': h.tolist(), 'k': k.tolist(), 'J_lo_float': v}, fh)


if __name__ == '__main__':
    main()
