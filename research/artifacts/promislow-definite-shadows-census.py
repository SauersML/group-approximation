#!/usr/bin/env python3
"""Definite-line shadows modulo 2 of the 52 radius-four census units of F_2[P].

Model (s, t)(s', t') = (ss', t + s t'), a = ((1,-1,-1),(1,1,0)), b = ((-1,1,-1),(0,1,1)).
Every census unit is the sum of the 21 elements of its support (coefficients in F_2).
Usage: hlku-census.py census52.json census_pairs.json
"""
import json, sys, hashlib
P = 2
SIGNS = {(1, 1, 1): 'e', (1, -1, -1): 'A', (-1, 1, -1): 'B', (-1, -1, 1): 'C'}
REPT = {'e': (0, 0, 0), 'A': (1, 1, 0), 'B': (0, 1, 1), 'C': (1, 0, -1)}
def mul(g, h): return (tuple(p * q for p, q in zip(g[0], h[0])), tuple(t + p * q for t, p, q in zip(g[1], g[0], h[1])))
a = ((1, -1, -1), (1, 1, 0)); b = ((-1, 1, -1), (0, 1, 1))
assert mul(a, b) == ((-1, -1, 1), REPT['C'])
def decompose(g):
    s, t = tuple(g[0]), tuple(g[1]); c = SIGNS[s]
    tau = tuple(t[i] - REPT[c][i] for i in range(3))
    assert all(v % 2 == 0 for v in tau), g
    return (tau[0] // 2, tau[1] // 2, -tau[2] // 2), c
def lred(A): return {k: v % P for k, v in A.items() if v % P}
def ladd(A, B):
    out = dict(A)
    for k, v in B.items(): out[k] = out.get(k, 0) + v
    return lred(out)
def lmul(A, B):
    out = {}
    for k1, v1 in A.items():
        for k2, v2 in B.items(): out[k1 + k2] = out.get(k1 + k2, 0) + v1 * v2
    return lred(out)
def lbar(A): return {-k: v for k, v in A.items()}
def lshift(A, e, c=1): return {k + e: c * v for k, v in A.items()}
def dmul(X, Y):
    (l0, l1), (m0, m1) = X, Y
    return (ladd(lmul(l0, m0), lshift(lmul(l1, lbar(m1)), 0, -1)), ladd(lmul(l0, m1), lmul(l1, lbar(m0))))
def dnorm(X): return ladd(lmul(X[0], lbar(X[0])), lmul(X[1], lbar(X[1])))
def spec_line(F, line):
    out = {}
    for (i, j, k), v in F.items():
        if line == 'C': sc, e = (-1) ** ((i + j) % 2), 2 * k
        elif line == 'A': sc, e = (-1) ** ((j + k) % 2), 2 * i
        else: sc, e = (-1) ** ((i + k) % 2), 2 * j
        out[e] = out.get(e, 0) + sc * v
    return out
def shadow(support, line):
    pqrs = [{}, {}, {}, {}]; idx = {'e': 0, 'A': 1, 'B': 2, 'C': 3}
    for g in support:
        m, c = decompose(g); d = pqrs[idx[c]]; d[m] = d.get(m, 0) + 1
    p, q, r, s = [spec_line(f, line) for f in pqrs]
    if line == 'C': return (ladd(p, lshift(s, 1)), ladd(q, lshift(r, -1, -1)))
    if line == 'A': return (ladd(p, lshift(q, 1)), ladd(r, lshift(s, 1)))
    return (ladd(p, lshift(r, 1)), ladd(q, lshift(s, -1)))
def monomial(X): return len(X[0]) + len(X[1]) == 1
units = json.load(open(sys.argv[1])); pairs = json.load(open(sys.argv[2]))
print('md5', sys.argv[1], hashlib.md5(open(sys.argv[1], 'rb').read()).hexdigest())
print('md5', sys.argv[2], hashlib.md5(open(sys.argv[2], 'rb').read()).hexdigest())
assert len(units) == 52 and all(len(u) == 21 for u in units)
# consistency gate: shadows of the 7 representative pairs (S, T) multiply to 1 on every line
for k, e in enumerate(pairs):
    for line in 'CAB':
        X, Y = shadow(e['S'], line), shadow(e['T'], line)
        assert dmul(X, Y) == ({0: 1}, {}) and dmul(Y, X) == ({0: 1}, {}), (k, line)
        assert dnorm(X) == {0: 1}
    print('rep %d (orbit size %d): shadows %s' % (k, e['size'], {line: ('monomial' if monomial(shadow(e['S'], line)) else 'NOT monomial') for line in 'CAB'}))
killed = 0; pattern = {}
for u in units:
    lines = tuple(line for line in 'CAB' if not monomial(shadow(u, line)))
    for line in 'CAB': assert dnorm(shadow(u, line)) == {0: 1}
    pattern[lines] = pattern.get(lines, 0) + 1
    killed += bool(lines)
print('52 census units: non-monomial line patterns', pattern)
print('units with a non-monomial shadow on some definite line:', killed, 'of 52')
print('DONE')
