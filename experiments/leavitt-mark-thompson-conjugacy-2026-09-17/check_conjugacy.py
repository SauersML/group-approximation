#!/usr/bin/env python3
"""Exact check: the Leavitt mark z = x_13(s_1 t_1) of St_20(L_2), transported to
R^x through a 20-word complete prefix code, is conjugate in R^x to the Thompson
cylinder swap v = s_00 t_01 + s_01 t_00 + s_1 t_1.

R = L_(F_2)(1,2).  Elements are F_2-combinations of monomials s_alpha t_beta,
stored as a set of (alpha, beta) pairs (coefficients mod 2).

Equality test (complete, not heuristic).  Refine every monomial so that
|beta| = N (s_a t_b = s_a0 t_b0 + s_a1 t_b1).  Then an element is
sum_{|w|=N} x_w t_w with x_w in span{s_alpha}.  Two elements are equal iff all
x_w agree, and x_w is read off exactly as the set of alpha with odd coefficient.
(This is the action on w.Y for an aperiodic tail Y, where distinct alpha give
distinct alpha.Y; L_2 is simple, so the action is faithful.)
"""
from itertools import product


def mul(x, y):
    out = set()
    for (a, b) in x:
        for (c, d) in y:
            # t_b s_c
            if c.startswith(b):
                term = (a + c[len(b):], d)
            elif b.startswith(c):
                term = (a, d + b[len(c):])
            else:
                continue
            out ^= {term}
    return out


def add(*xs):
    out = set()
    for x in xs:
        for m in x:
            out ^= {m}
    return out


def s(w):
    return {(w, "")}


def t(w):
    return {("", w)}


def st(a, b):
    return {(a, b)}


ONE = {("", "")}


def normal(x):
    N = max([len(b) for (_, b) in x] + [0])
    out = set()
    for (a, b) in x:
        k = N - len(b)
        for tail in product("01", repeat=k):
            tl = "".join(tail)
            out ^= {(a + tl, b + tl)}
    return N, out


def equal(x, y):
    d = add(x, y)
    return len(normal(d)[1]) == 0


def complete_code(n):
    code = ["0", "1"]
    while len(code) < n:
        m = min(len(w) for w in code)
        i = next(i for i, w in enumerate(code) if len(w) == m)
        w = code.pop(i)
        code[i:i] = [w + "0", w + "1"]
    return code


def main():
    c = complete_code(20)
    assert len(c) == 20
    # ring isomorphism M_20(R) -> R, E_ij r -> s_{c_i} r t_{c_j}
    # z = x_13(s_1 t_1)  ->  1 + s_{c_1} s_1 t_1 t_{c_3} = 1 + s_a t_b
    a, b = c[0] + "1", c[2] + "1"
    Z = add(ONE, st(a, b))
    assert equal(mul(Z, Z), ONE), "z is an involution"
    V = add(st("00", "01"), st("01", "00"), st("1", "1"))
    assert equal(mul(V, V), ONE)
    assert equal(V, add(ONE, mul(add(s("00"), s("01")), add(t("00"), t("01")))))
    # complement code W of {a, b}; complete code d of the same size for D' = s_1 R
    W = [c[0] + "0", c[2] + "0"] + [c[i] for i in range(20) if i not in (0, 2)]
    d = complete_code(len(W))
    U = add(mul(s("01"), t(b)), mul(add(s("00"), s("01")), t(a)),
            *[st("1" + d[i], W[i]) for i in range(len(W))])
    Ui = add(mul(s(b), add(t("00"), t("01"))), mul(s(a), t("00")),
             *[st(W[i], "1" + d[i]) for i in range(len(W))])
    assert equal(mul(U, Ui), ONE), "U Ui = 1"
    assert equal(mul(Ui, U), ONE), "Ui U = 1"
    assert equal(mul(mul(U, Z), Ui), V), "U z U^-1 = v"
    # negative controls: the test separates distinct elements
    assert not equal(Z, ONE) and not equal(V, ONE) and not equal(Z, V)
    assert not equal(mul(mul(Ui, Z), U), V)
    print("code c =", c)
    print("a =", a, " b =", b)
    print("OK: u z u^-1 = v = s_00 t_01 + s_01 t_00 + s_1 t_1 in R^x")


if __name__ == "__main__":
    main()
