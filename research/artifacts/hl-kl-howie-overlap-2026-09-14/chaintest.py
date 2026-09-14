#!/usr/bin/env python3
# Model test for the level-chain Tietze reduction (lane hl-kl-howie-overlap).
# P = H<a>, a normalizes H, a^n in H (n minimal), w = t a V(t) b, V in H*<t>, ab in H.
# t_i = a^i t a^-i, r_i = t_i V_{i+1}(t_{i+1}) h_i, h_i = a^i (ab) a^-i, t_n = z t_0 z^-1, z = a^n.
# Chain: t_i = (V_{i+1}(t_{i+1}) h_i)^-1 for i <= n-2, R(s) = s V_n(z Phi(s) z^-1) h_{n-1}.
# Checks: for g in H with w(g) = 1, s = a^(n-1) g a^-(n-1) gives Phi-chain t_i = a^i g a^-i and R(s) = 1.
# Also checks the exponent bookkeeping: deg_s R = 1 - (-d)^n with d = deg_t V, computed symbolically.
import random, itertools

def mul(p, q):  # apply q first, then p
    return tuple(p[i] for i in q)

def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)

def pw(p, k):
    e = tuple(range(len(p)))
    base = p if k >= 0 else inv(p)
    for _ in range(abs(k)):
        e = mul(e, base)
    return e

def gen_group(gens):
    e = tuple(range(len(gens[0])))
    seen = {e}
    frontier = [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in seen:
                    seen.add(y); nxt.append(y)
        frontier = nxt
    return seen

def conj(x, c):
    return mul(mul(x, c), inv(x))

def ev(word, j, a, s):  # V_j(s): coefficients conjugated by a^j, t -> s
    e = tuple(range(len(a)))
    aj = pw(a, j)
    out = e
    for kind, val in word:
        out = mul(out, conj(aj, val) if kind == 'c' else pw(s, val))
    return out

def deg(word):
    return sum(v for k, v in word if k == 't')

def run_case(name, H, a, trials, rng):
    Hl = sorted(H)
    e = tuple(range(len(a)))
    n = 1
    while pw(a, n) not in H:
        n += 1
    z = pw(a, n)
    fails = 0
    for _ in range(trials):
        L = rng.randint(1, 6)
        V = []
        for _ in range(L):
            V.append(('c', rng.choice(Hl)))
            V.append(('t', rng.choice([1, -1, 2, -2])))
        V.append(('c', rng.choice(Hl)))
        g = rng.choice(Hl)
        b = inv(mul(mul(g, a), ev(V, 0, a, g)))       # forces w(g) = g a V(g) b = 1
        ab = mul(a, b)
        assert ab in H, "ab not in H"
        w_g = mul(mul(mul(g, a), ev(V, 0, a, g)), b)
        assert w_g == e
        h = [conj(pw(a, i), ab) for i in range(n)]
        s = conj(pw(a, n - 1), g)
        t = {n - 1: s}
        for i in range(n - 2, -1, -1):
            t[i] = inv(mul(ev(V, i + 1, a, t[i + 1]), h[i]))
        ok_chain = all(t[i] == conj(pw(a, i), g) for i in range(n))
        R = mul(mul(s, ev(V, n, a, conj(z, t[0]))), h[n - 1]) if n >= 2 else mul(mul(t[0], ev(V, 1, a, conj(z, t[0]))), h[0])
        ok_R = (R == e)
        # every r_i vanishes on the chain values
        tn = conj(z, t[0])
        ok_r = all(mul(mul(t[i], ev(V, i + 1, a, t[i + 1] if i + 1 < n else tn)), h[i]) == e for i in range(n))
        if not (ok_chain and ok_R and ok_r):
            fails += 1
    print(f"{name}: n={n} z_is_1={z == e} trials={trials} failures={fails}")
    return fails

def symbolic_degree(d, n):
    # degree of t_{n-1} in R: t_i has degree -d * deg(t_{i+1}) for i <= n-2, deg t_{n-1} = 1
    dg = {n - 1: 1}
    for i in range(n - 2, -1, -1):
        dg[i] = -d * dg[i + 1]
    return 1 + d * dg[0] if n >= 2 else 1 + d

rng = random.Random(20260914)
total = 0
S4 = lambda *cyc: None
# G = S_4 on {0,1,2,3}
def perm_from_cycles(cycles, N):
    p = list(range(N))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)
V4 = gen_group([perm_from_cycles([(0, 1), (2, 3)], 4), perm_from_cycles([(0, 2), (1, 3)], 4)])
A4 = gen_group([perm_from_cycles([(0, 1, 2)], 4), perm_from_cycles([(1, 2, 3)], 4)])
A5 = gen_group([perm_from_cycles([(0, 1, 2, 3, 4)], 5), perm_from_cycles([(0, 1, 2)], 5)])
total += run_case("S4: H=V4, a=(0123), a^2 in H, z!=1", V4, perm_from_cycles([(0, 1, 2, 3)], 4), 400, rng)
total += run_case("A4: H=V4, a=(012), n=3", V4, perm_from_cycles([(0, 1, 2)], 4), 400, rng)
total += run_case("S4: H=A4, a=(01), n=2", A4, perm_from_cycles([(0, 1)], 4), 400, rng)
total += run_case("S5: H=A5, a=(01)(234)... n=2 via (01)", A5, perm_from_cycles([(0, 1)], 5), 400, rng)
# C_8 wreath-like: H = <x^4> inside <x> on 8 points, a = x, n = 4, z = x^4 != 1
x8 = perm_from_cycles([(0, 1, 2, 3, 4, 5, 6, 7)], 8)
total += run_case("C8: H=<x^4>, a=x, n=4, z!=1", gen_group([pw(x8, 4)]), x8, 200, rng)
# H = A_4 x? use S_4 x C_3-type: a = (0123) on S4 acting on H=A4? a normalizes A4, a^2 in A4 -> n=2
total += run_case("S4: H=A4, a=(0123), z=(02)(13)", A4, perm_from_cycles([(0, 1, 2, 3)], 4), 400, rng)
for d in (0, -2, 1, 2, -1):
    print("deg R for d=%d:" % d, [symbolic_degree(d, n) for n in range(1, 6)], "formula", [1 - (-d) ** n for n in range(1, 6)])
print("TOTAL_FAILURES", total)
