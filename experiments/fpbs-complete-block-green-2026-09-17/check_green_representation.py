#!/usr/bin/env python3
"""Numerical checks for fpbs-complete-block-free-products-satisfy-identity-e.

Group: Gamma = A_1 * ... * A_m, each factor either
  ('K', n): Z/n with generating set Z/n minus {0}; its Cayley graph is K_n;
  ('Z',)  : Z with generators +1, -1; its Cayley graph is a line.

Checks, for several factor lists and several p:
 (1) t_n(p) = P(0 <-> 1 in Bernoulli(p) on K_n) by enumeration, and t_3 = p + p^2 - p^3.
 (2) the local identity  kappa - mu * kappa = c delta_e  on every reduced word of
     length <= L, where kappa(x) = prod of letter weights (the two-point function) and
     mu = sum_i w_i(p) 1_{A_i \ e} with the explicit weights of Lemma 1.
 (3) ||mu||_1 = 1 - c / ||kappa||_1 below p_c, with ||kappa||_1 = 1/(1 - Phi).
 (4) kappa = c * G_mu at a small p: truncated Neumann series on a ball.
 (5) T_3 = (Z/2)^{*3}: w(p) = p/(1+2p^2) peaks at p = 1/sqrt 2 = p_{2->2}(T_3).
"""
import itertools
import math


def t_block(n, p):
    """P(0 <-> 1) in Bernoulli(p) bond percolation on K_n (exact enumeration)."""
    if n == 2:
        return p
    edges = [(a, b) for a in range(n) for b in range(a + 1, n)]
    tot = 0.0
    for conf in itertools.product([0, 1], repeat=len(edges)):
        par = list(range(n))

        def find(a):
            while par[a] != a:
                par[a] = par[par[a]]
                a = par[a]
            return a
        k = sum(conf)
        for e, o in zip(edges, conf):
            if o:
                par[find(e[0])] = find(e[1])
        if find(0) == find(1):
            tot += p ** k * (1 - p) ** (len(edges) - k)
    return tot


def weights(factors, p):
    """Lemma 1 weights w_i(p) and constant c(p)."""
    ts, betas = [], []
    for f in factors:
        if f[0] == 'K':
            n = f[1]
            t = t_block(n, p)
            beta = (n - 1) * t * t / (1 + (n - 2) * t)
        else:
            t = p
            beta = 2 * t * t / (1 + t * t)
        ts.append(t)
        betas.append(beta)
    B = sum(b / (1 - b) for b in betas)
    ws = []
    for f, t, b in zip(factors, ts, betas):
        den = (1 + (f[1] - 2) * t) if f[0] == 'K' else (1 + t * t)
        ws.append(t / (den * (1 - b) * (1 + B)))
    return ts, ws, 1.0 / (1 + B)


def gens(factors):
    out = []
    for i, f in enumerate(factors):
        if f[0] == 'K':
            out += [(i, g) for g in range(1, f[1])]
        else:
            out += [(i, 1), (i, -1)]
    return out


def lmul(factors, y, x):
    """Reduced word of y*x, y a single letter (i,g)."""
    i, g = y
    if x and x[0][0] == i:
        h = g + x[0][1]
        if factors[i][0] == 'K':
            h %= factors[i][1]
        if h == 0:
            return x[1:]
        return ((i, h),) + x[1:]
    return (y,) + x


def inv(factors, y):
    i, g = y
    return (i, (-g) % factors[i][1]) if factors[i][0] == 'K' else (i, -g)


def kappa(factors, ts, x):
    v = 1.0
    for i, g in x:
        v *= ts[i] ** (1 if factors[i][0] == 'K' else abs(g))
    return v


def length(factors, x):
    return sum(1 if factors[i][0] == 'K' else abs(g) for i, g in x)


def ball(factors, L):
    words = {()}
    frontier = {()}
    for _ in range(L):
        new = set()
        for x in frontier:
            for y in gens(factors):
                z = lmul(factors, y, x)
                if length(factors, z) <= L and z not in words:
                    new.add(z)
        words |= new
        frontier = new
    return words


def check_identity(factors, p, L):
    ts, ws, c = weights(factors, p)
    worst = 0.0
    for x in ball(factors, L):
        s = kappa(factors, ts, x)
        for y in gens(factors):
            s -= ws[y[0]] * kappa(factors, ts, lmul(factors, inv(factors, y), x))
        target = c if x == () else 0.0
        worst = max(worst, abs(s - target))
    return worst


def l1_data(factors, p):
    ts, ws, c = weights(factors, p)
    phi = 0.0
    mu1 = 0.0
    for f, t, w in zip(factors, ts, ws):
        u = (f[1] - 1) * t if f[0] == 'K' else 2 * t / (1 - t)
        phi += u / (1 + u)
        mu1 += (f[1] - 1) * w if f[0] == 'K' else 2 * w
    return phi, mu1, c


def neumann_check(factors, p, R, steps):
    ts, ws, c = weights(factors, p)
    v = {(): 1.0}
    G = {(): 1.0}
    for _ in range(steps):
        nv = {}
        for x, val in v.items():
            for y in gens(factors):
                z = lmul(factors, y, x)
                if length(factors, z) <= R:
                    nv[z] = nv.get(z, 0.0) + ws[y[0]] * val
        v = nv
        for z, val in v.items():
            G[z] = G.get(z, 0.0) + val
    worst = 0.0
    for x in ball(factors, 2):
        worst = max(worst, abs(c * G.get(x, 0.0) - kappa(factors, ts, x)))
    return worst


if __name__ == '__main__':
    for p in [0.1, 0.37, 0.8]:
        t3 = t_block(3, p)
        print(f"(1) p={p}: t_3 enumerated {t3:.12f}, p+p^2-p^3 = {p + p*p - p**3:.12f}")
    cases = [
        [('K', 2), ('K', 3)],
        [('K', 2), ('K', 2), ('K', 3)],
        [('Z',), ('K', 3)],
        [('K', 4), ('K', 2)],
        [('Z',), ('Z',)],
    ]
    for fac in cases:
        for p in [0.15, 0.3, 0.5, 0.9]:
            print(f"(2) {fac} p={p}: max |kappa - mu*kappa - c delta| on ball(6) = "
                  f"{check_identity(fac, p, 6):.2e}")
    for fac in cases:
        for p in [0.05, 0.1, 0.2]:
            phi, mu1, c = l1_data(fac, p)
            if phi < 1:
                k1 = 1 / (1 - phi)
                print(f"(3) {fac} p={p}: ||mu||_1 = {mu1:.12f}, 1 - c/||kappa||_1 = {1 - c / k1:.12f}")
    for fac in [[('K', 2), ('K', 3)], [('Z',), ('K', 3)]]:
        p = 0.1
        print(f"(4) {fac} p={p}: max |c G_mu - kappa| on ball(2) = {neumann_check(fac, p, 9, 40):.2e}")
    grid = [k / 1000 for k in range(1, 1000)]
    wv = [weights([('K', 2)] * 3, p)[1][0] for p in grid]
    k = max(range(len(grid)), key=lambda j: wv[j])
    print(f"(5) T_3: argmax w(p) = {grid[k]:.3f} (1/sqrt2 = {1/math.sqrt(2):.3f}); "
          f"max w = {wv[k]:.6f}, 3 w * (2 sqrt2 / 3) = {2*math.sqrt(2)*wv[k]:.6f}")
