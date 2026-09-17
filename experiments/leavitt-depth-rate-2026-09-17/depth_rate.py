#!/usr/bin/env python3
"""Calibration of the depth-growth and support-growth rates of units of the
binary Leavitt algebra L = L_{F_2}(1,2), acting on the Cantor module C({0,1}^N, F_2).

An element of L is a set of monomials (p, q), each meaning x_p y_q, with
(x_p y_q f)(w) = [w starts with p] * f(q . w[len p:]), and coefficients in F_2.
A locally constant function is stored as (k, table): it depends on the first k
letters, and table[i] is its value on the word of length k with binary index i.

For each unit u this script prints, for n = 1..NMAX:
  D(n) = max over cylinders C of length <= K0 of depth(u^n 1_C) - depth(1_C),
  M(n) = max over the same cylinders of mu(supp u^n 1_C) / mu(C).
Rates: D(n)/n -> delta(u), log2 M(n)/n -> lambda(u).  The obstruction theorem
says delta = lambda = 0 for any unit conjugate to a proper power.

Run: nice -n 10 timeout 1200 python3 depth_rate.py
"""
import math, random, sys

def word_bits(i, k):
    return [(i >> (k - 1 - j)) & 1 for j in range(k)]

def index(bits):
    v = 0
    for b in bits:
        v = 2 * v + b
    return v

def reduce_fn(k, tab):
    # drop trailing coordinates the function does not depend on
    while k > 0:
        ok = all(tab[2 * i] == tab[2 * i + 1] for i in range(1 << (k - 1)))
        if not ok:
            break
        tab = [tab[2 * i] for i in range(1 << (k - 1))]
        k -= 1
    return k, tab

def apply(elem, f):
    k, tab = f
    kout = max(len(p) + max(k - len(q), 0) for (p, q) in elem)
    kout = max(kout, max(len(p) for (p, q) in elem))
    out = [0] * (1 << kout)
    for (p, q) in elem:
        lp = len(p)
        for i in range(1 << kout):
            w = word_bits(i, kout)
            if w[:lp] != list(p):
                continue
            arg = list(q) + w[lp:]
            out[i] ^= tab[index(arg[:k])] if k > 0 else tab[0]
    return reduce_fn(kout, out)

def measure(f):
    k, tab = f
    return sum(tab) / (1 << k)

def cylinder(bits):
    k = len(bits)
    tab = [0] * (1 << k)
    tab[index(bits)] = 1
    return (k, tab)

def w(s):
    return tuple(int(c) for c in s)

UNITS = {
    # Thompson F generator x0 (infinite order): leaves 0->00, 10->01, 11->1;
    # the operator f -> f o v^-1 is sum x_range y_domain.
    "thompson_x0": ([(w("00"), w("0")), (w("01"), w("10")), (w("1"), w("11"))],
                    [(w("0"), w("00")), (w("10"), w("01")), (w("11"), w("1"))]),
    # torsion element of V: swap the two halves
    "swap_order2": ([(w("0"), w("1")), (w("1"), w("0"))],
                    [(w("0"), w("1")), (w("1"), w("0"))]),
    # [[T,1],[1,0]] in GL_2(F_2[T]) with T = x_0, via M_2(L) = L
    # (x0 p y0 + x0 q y1 + x1 r y0 + x1 s y1); inverse [[0,1],[1,T]].
    "gl2_fibonacci": ([(w("00"), w("0")), (w("0"), w("1")), (w("1"), w("0"))],
                      [(w("0"), w("1")), (w("1"), w("0")), (w("10"), w("1"))]),
}

def check_unit(u, uinv, trials=20, k=6):
    rnd = random.Random(1)
    for _ in range(trials):
        f = reduce_fn(k, [rnd.randint(0, 1) for _ in range(1 << k)])
        g = apply(uinv, apply(u, f))
        h = apply(u, apply(uinv, f))
        for x in (g, h):
            kk = max(x[0], f[0])
            ex = lambda F: [F[1][i >> (kk - F[0])] for i in range(1 << kk)]
            if ex(x) != ex(f):
                return False
    return True

def rates(u, nmax, k0=3, cap=17):
    cyls = [cylinder(word_bits(i, k)) for k in range(1, k0 + 1) for i in range(1 << k)]
    cur = cyls[:]
    rows = []
    for n in range(1, nmax + 1):
        cur = [apply(u, f) for f in cur]
        D = max(f[0] - c[0] for f, c in zip(cur, cyls))
        M = max(measure(f) / measure(c) for f, c in zip(cur, cyls))
        rows.append((n, D, M))
        if max(f[0] for f in cur) > cap:
            break
    return rows

if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    for name, (u, uinv) in UNITS.items():
        print(f"== {name}: unit check {check_unit(u, uinv)}")
        for label, el in (("u", u), ("u^-1", uinv)):
            rows = rates(el, nmax)
            print(f"  {label}: " + "  ".join(f"n={n}:D={D},M={M:.3g}" for n, D, M in rows))
