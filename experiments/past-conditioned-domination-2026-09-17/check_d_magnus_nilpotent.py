#!/usr/bin/env python3
"""Exact check of past-conditioned domination
    D:  I(x_1 ; y_F | x_{<1}) <= H(y_1)
for NONLINEAR codes on F_2 = <a,b> in the Magnus order, together with the transfer used in the proof of
research/past-conditioned-domination-holds-on-locally-amenable-orders.md:

  * for every tested configuration, the smallest c such that the degree-c truncated Magnus map
    mu_c : F_2 -> (Z<X,Y>/deg>c)^x separates the sites S = FE u {1}; then the quotient
    N_c = F_2/D_{c+1} (a nilpotent group, the image of mu_c) carries the truncated-Magnus order, the
    quotient is injective on S and keeps the sign of every site, so the configuration is realized
    order-preservingly in an amenable left-ordered group, where D is a theorem;
  * the exact value of I - H(y_1) (x iid uniform bits, k = 1, q = 2), by enumerating x on S.

The theorem predicts gap <= 0 on every line.  Codes: all 254 nonconstant Boolean psi on |E| = 3 and 60 random
set partitions of {0,1}^3 into 2 or 3 blocks (non-Boolean outputs), for six windows.
usage: check_d_magnus_nilpotent.py [n_random_F] [seed]"""
import os, random, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-ordered-certificates-2026-09-17'))
from left_order_linear_domination import mul, ball, series_mul, gen_series, magnus_sign  # noqa: E402

LET = {'a': 1, 'A': -1, 'b': 2, 'B': -2}


def word(s):
    return tuple(LET[c] for c in s if c != '1')


def inv(w):
    return tuple(-s for s in reversed(w))


def show(w):
    r = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}
    return ''.join(r[s] for s in w) or '1'


def mu_trunc(w, c):
    S = {(): 1}
    for s in w:
        S = series_mul(S, gen_series(s, c), c)
    return frozenset((m, v) for m, v in S.items() if v)


def separating_degree(sites, cmax=12):
    for c in range(1, cmax + 1):
        imgs = {mu_trunc(s, c) for s in sites}
        if len(imgs) == len(sites):
            return c
    return None


def trunc_sign(w, c):
    """sign of w in the order of N_c: first nonzero coefficient of mu_c(w) - 1 in (degree, lex) order."""
    S = dict(mu_trunc(w, c))
    S[()] = S.get((), 0) - 1
    nz = sorted((m for m, v in S.items() if v), key=lambda m: (len(m), m))
    return 0 if not nz else (1 if S[nz[0]] > 0 else -1)


_SIGN = {}


def msign(w):
    # the leading Magnus degree of a nontrivial word is at most its length, so truncating there is exact
    if w not in _SIGN:
        _SIGN[w] = magnus_sign(w, len(w) + 1)
    return _SIGN[w]


def entropy_of_keys(keys):
    _, cnt = np.unique(keys, return_counts=True)
    p = cnt / cnt.sum()
    return float(-(p * np.log2(p)).sum())


def d_gap(E, F, psi_table, sites):
    """exact I(x_1; y_F | x_{P}) - H(y_1), P = past sites of S, psi_table indexed by the bits on E."""
    idx = {s: i for i, s in enumerate(sites)}
    n = len(sites)
    X = ((np.arange(1 << n)[:, None] >> np.arange(n)[None, :]) & 1).astype(np.int64)
    nout = int(max(psi_table)) + 1
    tab = np.array(psi_table, dtype=np.int64)
    yk = np.zeros(1 << n, dtype=np.int64)
    for f in F:
        code = np.zeros(1 << n, dtype=np.int64)
        for j, e in enumerate(E):
            code |= X[:, idx[mul(f, e)]] << j
        yk = yk * nout + tab[code]
    past = [idx[s] for s in sites if msign(s) < 0]
    pk = np.zeros(1 << n, dtype=np.int64)
    for i in past:
        pk = pk * 2 + X[:, i]
    one = X[:, idx[()]]
    # integer keys for (y_F, x_P) and (y_F, x_P, x_1)
    a = yk * (1 << len(past)) + pk
    ha = entropy_of_keys(a)
    hb = entropy_of_keys(a * 2 + one)
    I = 1.0 + ha - hb          # H(x_1 | x_P) = 1
    Hy1 = entropy_of_keys(tab)  # y_1 = psi of iid uniform bits on E
    return I - Hy1, I, Hy1


def random_partition(m, rng):
    labels, out = {}, []
    blocks = rng.randint(2, 4)
    for i in range(m):
        out.append(rng.randrange(blocks))
    # relabel to 0..
    for v in out:
        labels.setdefault(v, len(labels))
    return [labels[v] for v in out]


def main():
    nF = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    rng = random.Random(seed)
    windows = ['1,a,b', '1,a,ab', '1,a,ba', '1,a,Ab', '1,ab,ba', '1,a,aba']
    B2 = [w for w in ball(2)]
    worst = (-9, None)
    lines = 0
    viol = 0
    for Es in windows:
        E = [word(t) for t in Es.split(',')]
        readers = [inv(e) for e in E]
        Fs = [readers]
        for _ in range(nF):
            extra = rng.sample([w for w in B2 if w not in readers], rng.randint(1, 3))
            Fs.append(readers + extra)
        for F in Fs:
            sites = sorted({mul(f, e) for f in F for e in E} | {()}, key=lambda w: (len(w), w))
            if len(sites) > 16:
                continue
            c = separating_degree(sites)
            assert c is not None
            signs_ok = all(trunc_sign(s, c) == msign(s) for s in sites)
            assert signs_ok
            gmax = -9
            codes = [[(v >> t) & 1 for t in range(8)] for v in range(1, 255)]
            codes += [random_partition(8, rng) for _ in range(60)]
            for tab in codes:
                g, I, H = d_gap(E, F, tab, sites)
                lines += 1
                if g > 1e-9:
                    viol += 1
                    print('VIOLATION', Es, [show(f) for f in F], tab, I, H)
                if g > gmax:
                    gmax = g
                if g > worst[0]:
                    worst = (g, (Es, [show(f) for f in F], tab, I, H))
            print('E=%-9s |F|=%d |S|=%2d separating degree c=%d signs preserved=%s  max(I-H(y1))=%+.6f'
                  % (Es, len(F), len(sites), c, signs_ok, gmax))
    print('configurations x codes tested: %d, violations: %d' % (lines, viol))
    print('worst gap %+.3e at %s' % (worst[0], worst[1]))


if __name__ == '__main__':
    main()
