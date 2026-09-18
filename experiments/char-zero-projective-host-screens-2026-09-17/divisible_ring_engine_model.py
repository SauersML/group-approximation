#!/usr/bin/env python3
"""Model check for the finitely presented divisible ring engine D.

D = Z< s, t, w, v, b, a > modulo
  R1  s t = 1,  t s = 1
  R2  v w = 1
  R3  s (w v) t = 1 - w v
  R4  b (w v) = (w v) b
  R5  v b w = b + 1
  R6  b (1 - w v) = 1 - w v
  R7  a b = 1

(t is the inverse of s, v plays w-bar.)  The written derivation shows that
    y_k := v^k a w^k o + s v^k a w^k o t,   o := 1 - w v,
satisfies (k+1) y_k = 1 in D, for every k >= 0.  So D is a Q-algebra.

This script checks, on the explicit representation on the Q-vector space
with basis e_x, x in Z \\ {0}, that
  * all seven relations hold on every basis vector in a test window,
  * the unit acts as the identity (so the representation is unital and D != 0),
  * (k+1) y_k acts as the identity for k = 0..K (sanity check of the derivation,
    evaluated in the model rather than symbolically).

Representation:
  sigma : Z\\{0} -> Z\\{0} is the involution 2m <-> 2m-1 (m >= 1), -2m <-> -(2m-1),
          which swaps even and odd nonzero integers;
  s = t = permutation by sigma;
  w e_x = e_{2x};   v e_{2x} = e_x,  v e_odd = 0;
  b e_x = (nu_2(x)+1) e_x;   a e_x = e_x / (nu_2(x)+1).
Run:  python3 divisible_ring_engine_model.py
"""
from fractions import Fraction
from collections import defaultdict


def nu2(x):
    x = abs(x)
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


def sigma(x):
    if x > 0:
        return x - 1 if x % 2 == 0 else x + 1
    y = -x
    return -(y - 1) if y % 2 == 0 else -(y + 1)


def clean(vec):
    return {x: c for x, c in vec.items() if c != 0}


def add(u, u2, coeff=1):
    out = defaultdict(Fraction, u)
    for x, c in u2.items():
        out[x] += coeff * c
    return clean(out)


def S(vec):
    return clean({sigma(x): c for x, c in vec.items()})


T = S  # sigma is an involution


def W(vec):
    return clean({2 * x: c for x, c in vec.items()})


def V(vec):
    return clean({x // 2: c for x, c in vec.items() if x % 2 == 0})


def B(vec):
    return clean({x: c * (nu2(x) + 1) for x, c in vec.items()})


def A(vec):
    return clean({x: c / (nu2(x) + 1) for x, c in vec.items()})


def ONE(vec):
    return dict(vec)


def comp(*ops):
    """comp(f, g, h)(u) = f(g(h(u))), i.e. the ring product f g h."""
    def run(vec):
        for op in reversed(ops):
            vec = op(vec)
        return vec
    return run


def lin(*terms):
    """Linear combination of operators: lin((c1, op1), (c2, op2), ...)."""
    def run(vec):
        out = {}
        for c, op in terms:
            out = add(out, op(vec), c)
        return out
    return run


def e(x):
    return {x: Fraction(1)}


def assert_equal_ops(name, lhs, rhs, window):
    for x in window:
        if lhs(e(x)) != rhs(e(x)):
            raise AssertionError(f"{name} fails on e_{x}: {lhs(e(x))} != {rhs(e(x))}")
    print(f"ok  {name}")


def main():
    window = [x for x in range(-257, 258) if x != 0]
    # sanity: sigma is a bijection swapping parity
    assert all(sigma(sigma(x)) == x and (sigma(x) % 2) != (x % 2) for x in window)
    q = comp(W, V)
    o = lin((1, ONE), (-1, q))
    assert_equal_ops("R1 st=1", comp(S, T), ONE, window)
    assert_equal_ops("R1 ts=1", comp(T, S), ONE, window)
    assert_equal_ops("R2 vw=1", comp(V, W), ONE, window)
    assert_equal_ops("R3 s(wv)t=1-wv", comp(S, q, T), o, window)
    assert_equal_ops("R4 b(wv)=(wv)b", comp(B, q), comp(q, B), window)
    assert_equal_ops("R5 vbw=b+1", comp(V, B, W), lin((1, B), (1, ONE)), window)
    assert_equal_ops("R6 b(1-wv)=1-wv", comp(B, o), o, window)
    assert_equal_ops("R7 ab=1", comp(A, B), ONE, window)
    K = 12
    for k in range(K + 1):
        wk = comp(*([W] * k)) if k else ONE
        vk = comp(*([V] * k)) if k else ONE
        ck = comp(vk, A, wk)
        xk = comp(ck, o)
        yk = lin((1, xk), (1, comp(S, xk, T)))
        assert_equal_ops(f"(k+1) y_k = 1 for k={k}", lin((k + 1, yk)), ONE, window)
    print("all checks passed: the representation is unital and every tested integer is invertible")


if __name__ == "__main__":
    main()
