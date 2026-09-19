"""Exact check of the first two tower steps of the hyperseries construction for G(K; 1, beta).

Group law: g . h = g o h (composition).  A word l_1 l_2 ... maps to phi(l_1) o phi(l_2) o ...
Relation at step n (stable letter y_{n+1}):  y_{n+1}^{-b} y_{n-1} y_{n+1}^{b} = y_{n-1} y_n^K,
i.e. a o u = u o B with a = g_{n-1}, B = g_{n-1} o g_n^K, u = g_{n+1}^b.
The letters below are the ones the proof produces; later steps need hyperseries Abel functions.
Usage: python3 hyperseries_first_steps.py
"""
import sympy as sp

x, s = sp.symbols('x s', real=True)
X = sp.Symbol('X', positive=True)


def comp(f, g):          # f o g
    return sp.simplify(f.subs(x, g))


def power(f, k):
    out = x
    for _ in range(k):
        out = comp(out, f)
    return out


def check(K, beta, g, inv):
    """g: list of letters g_0..g_m; inv: their compositional inverses. Check relations n = 1..m-1."""
    for n in range(1, len(g) - 1):
        u = g[n + 1] if beta == 1 else inv[n + 1]
        uinv = inv[n + 1] if beta == 1 else g[n + 1]
        lhs = comp(uinv, comp(g[n - 1], u))
        rhs = comp(g[n - 1], power(g[n], K))
        ok = sp.simplify(sp.expand_log(lhs - rhs, force=True)) == 0
        sign = sp.limit(g[n + 1] - x, x, sp.oo)
        print(f"K={K} beta={beta} step y_{n+1}: relation {'OK' if ok else 'FAIL'}; "
              f"g_{n+1} - x -> {sign} (want {'-oo' if beta == 1 else 'oo'})")
        assert ok


for K in (2, 3):
    # beta = 1: all letters < x.  g0 = g1 = x - 1, g2 = x/(K+1), g3 = log(x + c)/log((K+1)^K) + s
    m = K + 1
    g2 = x / m
    M = m ** K                                 # g_1 o g_2^K = x/M - 1
    c = sp.Rational(M, M - 1)                  # solves log_M((x/M - 1) + c) = log_M(x + c) - 1
    g3 = sp.log(x + c) / sp.log(M) + s
    g = [x - 1, x - 1, g2, g3]
    inv = [x + 1, x + 1, m * x, sp.Pow(M, x - s) - c]
    check(K, 1, g, inv)
    # beta = -1: all letters > x.  g0 = g1 = x + 1, g2 = (K+1) (x - s0) with u = g2^{-1} = x/(K+1) + s0
    s0 = sp.Rational(1, 2)
    g = [x + 1, x + 1, m * (x - s0)]
    inv = [x - 1, x - 1, x / m + s0]
    check(K, -1, g, inv)
