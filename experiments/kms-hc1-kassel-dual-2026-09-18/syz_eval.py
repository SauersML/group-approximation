#!/usr/bin/env python3
"""Explicit-syzygy evaluation of the ca-edge defect from the seed pairing tables of fo_dual (SEEDS=1 PAIRTAB=1).

Usage: python3 syz_eval.py p pair00.txt pair10.txt pair01.txt
(the three tables are fo_dual runs on the slice (p,1,p) with (alphaA,alphaB) = (0,0), (1,0), (0,1)).

u(h) = restricted Heisenberg algebra of a = rho(Y_a) = E12, c = rho(Y_c) = E31 t, e = ca - ac = E32 t (central),
PBW basis c^j e^k a^i (exponents < p).  In multidegree (p,p) of (a,c) its basis is v_k = c^(p-k) e^k a^(p-k), k=1..p-1.
The raw lowest forms of the two seeds end in b as  f_[a,b,a]{210} = l1 a^2 b + (words ending in a),
f_[b,c,c]{012} = l2 c^2 b + (words ending in c).  A pair (U1,U2) with l1 U1 a^2 + l2 U2 c^2 = 0 in u(h) is a syzygy
of the edge slice and its first-order value is zeta = psi(U1 X_210) + psi(U2 X_012).
With U2 = sum_k g_k c^(p-2-k) e^k a^(p-k) (k=1..p-2):
  U2 c^2 = sum_k g_k (v_k - 2(p-k) v_(k+1) + (p-k)(p-k-1) v_(k+2)),
the v_(p-1) coefficient must vanish (v_(p-1) is not in u(h) a^2) and U1 = -(l2/l1) sum_(m<=p-2) d_m c^(p-m) e^m a^(p-2-m).
The script prints zeta, as the linear form kappa*v00 + alphaA*(v10-v00) + alphaB*(v01-v00), on a basis of the syzygies.
"""
import re, sys

p = int(sys.argv[1]); files = sys.argv[2:5]

def load(fn):
    pair, lam = {}, {}
    for line in open(fn):
        m = re.match(r'PAIR (\S+) c\^(\d+) e\^(\d+) a\^(\d+) : (\d+)', line)
        if m: pair[(m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)))] = int(m.group(5)); continue
        m = re.match(r'SEEDGEN (\S+) mu \S+ f0:(.*?)  X=', line)
        if m:
            for t in m.group(2).split():
                c, w = t.split('*')
                if w in ('aab', 'ccb'): lam[m.group(1)] = int(c)
    return pair, lam

tabs = [load(f) for f in files]
S1, S2 = '[a,b,a]{210}', '[b,c,c]{012}'
l1, l2 = tabs[0][1][S1], tabs[0][1][S2]
r = (-l2 * pow(l1, -1, p)) % p          # U1 a^2 = r * U2 c^2

def zeta(g, tab):
    d = [0] * (p + 2)
    for k in range(1, p - 1):
        if not g[k]: continue
        d[k] += g[k]; d[k + 1] += g[k] * (-2 * (p - k)); d[k + 2] += g[k] * (p - k) * (p - k - 1)
    d = [x % p for x in d]
    assert d[p - 1] == 0, "not a syzygy"
    z = 0
    for m in range(1, p - 1):
        if d[m]: z += r * d[m] * tab[(S1, p - m, m, p - 2 - m)]
    for k in range(1, p - 1):
        if g[k]: z += g[k] * tab[(S2, p - 2 - k, k, p - k)]
    return z % p

def form(g):
    v = [zeta(g, t[0]) for t in tabs]
    return (v[0], (v[1] - v[0]) % p, (v[2] - v[0]) % p)

print(f"p={p}  l1={l1} l2={l2}  (U1 a^2 = {r} U2 c^2)")
basis = []
for k in range(1, p - 3):
    g = [0] * (p + 1); g[k] = 1; basis.append((f"g=e_{k}", g))
g = [0] * (p + 1); g[p - 3] = 2; g[p - 2] = 3; basis.append((f"g=2e_{p-3}+3e_{p-2}", g))
for name, g in basis:
    try: f = form(g)
    except KeyError: f = "pairings not in the tables (PAIRONLY run)"
    print(f"  syzygy {name:18s} zeta coords (v00, v10-v00, v01-v00) = {f}")
