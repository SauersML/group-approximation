#!/usr/bin/env python3
"""Exact spot checks for the Cantor model of Lodha's group S (arXiv:1710.06220).

Rational sequences are pairs (word, c): the finite 0/1 string `word` followed by c^infinity.
All maps act on the right; a product [g1, g2, ...] means apply g1 first.

Checks, on every rational sequence with a word of length <= 9 and either tail:
  1. Phi-intertwining of x, x_1, p_0, y_10 y_110^{-1} with a, b, l, s (Lodha l.390-413).
  2. y_u = x_u y_u0 y_u10^{-1} y_u11 and y_u^{-1} = x_u^{-1} y_u00^{-1} y_u01 y_u1^{-1}.
  3. w_{0,1} = x_0 x_1^{-1} w_{00,010} w_{011,100} w_{101,11}.
  4. w_{10,110} = x_110^{-1} w_{10,1101} w_{11001,11000}   (Lodha l.646).
  5. p_n = x_{1^n} p_{n+1} for n = 0..4.
  6. f^{-1} y_sigma f = y_{sigma.f} for sample tree-diagram maps f acting on sigma.
  7. y and y^{-1} fix 0^inf and 1^inf.
  8. conjugation by the digit flip sends y to y^{-1} and x to x^{-1}.
These are finite samples: evidence for the hand proofs in the artifact, not a proof.
"""
from fractions import Fraction
from itertools import product
import sys

INF = None  # the point at infinity of R u {infinity}


def canon(seq):
    w, c = seq
    while w and w[-1] == c:
        w = w[:-1]
    return (w, c)


def digit(seq, i):
    w, c = seq
    return w[i] if i < len(w) else c


def drop(seq, k):
    w, c = seq
    return (w[k:], c)


def has_prefix(seq, u):
    return all(digit(seq, i) == u[i] for i in range(len(u)))


def y_gen(seq, inverse=False):
    """y or y^{-1} applied to a rational sequence."""
    out = []
    state = inverse
    pos = 0
    w, c = seq
    while pos < len(w):
        if not state:  # y
            if digit(seq, pos) == '1':
                out.append('11'); pos += 1
            elif digit(seq, pos + 1) == '0':
                out.append('0'); pos += 2
            else:
                out.append('10'); pos += 2; state = True
        else:  # y^{-1}
            if digit(seq, pos) == '0':
                out.append('00'); pos += 1
            elif digit(seq, pos + 1) == '0':
                out.append('01'); pos += 2; state = False
            else:
                out.append('1'); pos += 2
    # remaining input is c^infinity, fixed by y and y^{-1}
    return canon((''.join(out), c))


def x_gen(seq, inverse=False):
    table = [('00', '0'), ('01', '10'), ('1', '11')]
    if inverse:
        table = [(t, s) for (s, t) in table]
    return prefix_map(seq, table)


def prefix_map(seq, table):
    for s, t in table:
        if has_prefix(seq, s):
            w, c = drop(seq, len(s))
            return canon((t + w, c))
    raise ValueError('prefix map does not act')


def localize(g, u):
    def h(seq):
        if has_prefix(seq, u):
            rest = g(drop(seq, len(u)))
            return canon((u + rest[0], rest[1]))
        return canon(seq)
    return h


def X(u, e=1):
    return localize(lambda q: x_gen(q, e < 0), u)


def Y(u, e=1):
    return localize(lambda q: y_gen(q, e < 0), u)


def W(s, t):
    return compose([Y(s, 1), Y(t, -1)])


def compose(gs):
    def h(seq):
        for g in gs:
            seq = g(seq)
        return seq
    return h


def p_table(n):
    if n == 0:
        return [('0', '1'), ('1', '0')]
    tab = [('1' * k + '0', '1' * (k + 1) + '0') for k in range(n)]
    tab.append(('1' * n + '0', '1' * (n + 1)))
    tab.append(('1' * (n + 1), '0'))
    return tab


def P(n, e=1):
    tab = p_table(n)
    if e < 0:
        tab = [(t, s) for (s, t) in tab]
    return lambda q: prefix_map(q, tab)


# ---- Phi and the circle maps ----

def small_phi(seq):
    w, c = seq
    val = Fraction(0) if c == '0' else INF
    for d in reversed(w):
        if d == '1':
            val = INF if val is INF else 1 + val
        else:
            val = Fraction(1) if val is INF else val / (1 + val)
    return val


def neg(v):
    return INF if v is INF else -v


def Phi(seq):
    d = digit(seq, 0)
    rest = drop(seq, 1)
    if d == '1':
        return small_phi(rest)
    w, c = rest
    flip = {'0': '1', '1': '0'}
    return neg(small_phi((''.join(flip[ch] for ch in w), flip[c])))


def a(t):
    return INF if t is INF else t + 1


def b(t):
    if t is INF or t >= 1:
        return a(t)
    if t <= 0:
        return t
    if t <= Fraction(1, 2):
        return t / (1 - t)
    return (3 * t - 1) / t


def l(t):
    if t is INF:
        return Fraction(0)
    if t == 0:
        return INF
    return -1 / t


def s_map(t):
    if t is INF or t <= 0 or t >= 2:
        return t
    if t <= 1:
        return 2 * t / (1 + t)
    return 2 / (3 - t)


def all_rational(maxlen):
    for n in range(maxlen + 1):
        for bits in product('01', repeat=n):
            for c in '01':
                yield canon((''.join(bits), c))


def main():
    seqs = sorted(set(all_rational(9)))
    fails = []

    def expect(name, lhs, rhs):
        for q in seqs:
            try:
                u, v = lhs(q), rhs(q)
            except ValueError:
                continue
            if u != v:
                fails.append((name, q, u, v))
                return

    # 1. intertwining
    gens = [('x~a', X(''), a), ('x_1~b', X('1'), b), ('p_0~l', P(0), l),
            ('y10y110^-1~s', W('10', '110'), s_map)]
    for name, g, circ in gens:
        expect('intertwine ' + name, lambda q, g=g: Phi(g(q)), lambda q, circ=circ: circ(Phi(q)))
    # 2. amplification
    for u in ['', '0', '1', '10', '011', '1101']:
        expect('amp+ ' + u, Y(u), compose([X(u), Y(u + '0'), Y(u + '10', -1), Y(u + '11')]))
        expect('amp- ' + u, Y(u, -1), compose([X(u, -1), Y(u + '00', -1), Y(u + '01'), Y(u + '1', -1)]))
    # 3, 4. decompositions
    expect('w01', W('0', '1'), compose([X('0'), X('1', -1), W('00', '010'), W('011', '100'), W('101', '11')]))
    expect('w10,110', W('10', '110'), compose([X('110', -1), W('10', '1101'), W('11001', '11000')]))
    # 5. p_n = x_{1^n} p_{n+1}
    for n in range(5):
        expect('p%d' % n, P(n), compose([X('1' * n), P(n + 1)]))
    # 6. conjugation by prefix maps acting on sigma
    samples = [(X(''), X('', -1), [('00', '0'), ('01', '10'), ('1', '11')]),
               (P(2), P(2, -1), p_table(2))]
    for f, finv, tab in samples:
        for sigma in ['000', '0110', '101', '1110', '11101']:
            img = next((t + sigma[len(s):] for s, t in tab if sigma.startswith(s)), None)
            if img is None:
                continue
            expect('conj ' + sigma, compose([finv, Y(sigma), f]), Y(img))
    # 8. digit flip conjugates y to y^{-1} and x to x^{-1} (used only in the G_0 remark)
    def flip(q):
        tr = {'0': '1', '1': '0'}
        return canon((''.join(tr[ch] for ch in q[0]), tr[q[1]]))
    expect('flip y', compose([flip, Y(''), flip]), Y('', -1))
    expect('flip x', compose([flip, X(''), flip]), X('', -1))
    # 7. fixed points
    for c in '01':
        for inv in (False, True):
            if y_gen(('', c), inv) != ('', c):
                fails.append(('fix', c, inv))
    print('rational sequences tested:', len(seqs))
    if fails:
        for f in fails:
            print('FAIL', f)
        sys.exit(1)
    print('all checks passed')


if __name__ == '__main__':
    main()
