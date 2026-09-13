---
rg: 2
id: murray-z-only-ansatz-has-no-char0-units-proof
kind: route
title: Reciprocal splitting and a Wronskian bound for Murray's z-only ansatz
target: murray-z-only-ansatz-has-no-char0-units
requires: []
---

Notation as in the target. `K` has characteristic 0, `R = K[z^{+-1}]`, and `*`
is the `K`-linear involution `z -> z^-1` of `R` and of `K(z)`. `R` is a UFD
whose units are the monomials `c z^j`, `c in K^x`. For `f != 0` in `R`,
`span f` is the highest exponent of `f` minus the lowest. It counts the zeros of
`f` in `Kbar^x` with multiplicity, so `span(fg) = span f + span g` and
`f | g != 0` gives `span f <= span g`. Also `span f^* = span f`. Write
`theta = z d/dz`. Because `char K = 0`, `theta` lowers the order of vanishing
of a nonzero rational function at a point `alpha in Kbar^x` by exactly one
when that order is positive, and a rational function killed by `theta` is
constant. `N_i = f_i^* f_i`; `N_i = 0` forces `f_i = 0`.

**Step 0: equations.** `u'u = 1` implies Murray's equations

    (1) N7 = 1
    (2) N2 = N4 = N6
    (3) N3 = N5 = f7^* f6 + f6^* f7 + 4 N6
    (4) N1 = f2^* f3 + f4^* f5
    (5) f2^* f5 = z f5^* f2 = f3^* f4 = z f4^* f3
                = (f6^* f1 + z f1^* f6) - (f2^* f4 + z f4^* f2)

(and a sixth, not used). Certificate: `murray-z-only-ansatz-check.py verify`
computes `u'u - 1` with the `f_i` and `f_i^*` as independent symbols and shows
that each equation lies in the `Q(z)`-span of the coefficients of `u'u - 1`
and their `*`-images. By (1), `f7 = e z^k` with `e = +-1`.

**Step 1: `f2 = 0`.** (2) gives `f4 = f6 = 0`, (3) gives `f3 = f5 = 0` and (4)
gives `f1 = 0`. Then `u = f7 ab = e z^k ab`. From now on `f2 != 0`, and we
derive a contradiction.

**Step 2: shape.** By (2) `f4 != 0`; put `rho = f4 / f2`. Then
`rho rho^* = N4 / N2 = 1`, so `(rho^-1)^* = rho`. Put `c = rho + z rho^-1`, so
`z c^* = c`.

- (5) gives `f2^* f5 = z f4^* f3 = z rho^-1 f2^* f3`, so `f5 = z rho^-1 f3`.
  Put `h = f2^* f3`. Then `f2^* f5 = z rho^-1 h` and `z f5^* f2 = rho h^*`,
  so (5) gives `h^* = z rho^-2 h`. Also `f4^* f5 = z rho^-2 h = h^*`, and (4)
  reads `N1 = h + h^* = z^-1 c (z rho^-1 h)`.
- `f2^* f4 + z f4^* f2 = c N2 = c N6`. Put `D = f1 - c f6`. Then
  `f6^* f1 + z f1^* f6 = f6^* D + z D^* f6 + 2 c N6`, and (5) gives
  `z rho^-1 h = f6^* D + z D^* f6 + c N6`.
- Expanding `f1 = D + c f6` gives
  `N1 = D^* D + z^-1 c (f6^* D + z D^* f6) + z^-1 c^2 N6`. By the first two
  bullets this equals `z^-1 c (f6^* D + z D^* f6) + z^-1 c^2 N6`, so
  `D^* D = 0` and `D = 0`. So `f1 = c f6` and `z rho^-1 h = c N2`.
- So `f2^* f3 = z^-1 rho c f2^* f2`, that is `f3 = z^-1 rho c f2` and
  `f5 = c f2`. Then `N3 = c c^* N2 = z^-1 c^2 N6`, and (3) gives

      g N6 = f7^* f6 + f6^* f7,   g = z^-1 c^2 - 4 = w + w^-1 - 2,   w = z^-1 rho^2.

**Step 3: `rho` in lowest terms.** Write `rho = A / B` with `gcd(A, B) = 1`.
From `A A^* = B B^*`, `A | B^*` and `B | A^*`, so `A` and `B^*` are associates.
Normalize `B in K[z]` with `B(0) != 0` and put `n = deg B = span B`. Then
`rho = mu z^s B^* / B` with `s in Z`, `mu^2 = rho rho^* = 1`, and
`gcd(B, B^*) = 1`. Put `Delta = B^2 - z^(2s-1) B^*2`.

- `gcd(B B^*, Delta) = 1`, because `Delta = -z^(2s-1) B^*2 mod B` and
  `Delta = B^2 mod B^*`.
- `span Delta >= 2n + 1`. The exponents of `B^2` run exactly from `0` to `2n`,
  and those of `z^(2s-1) B^*2` exactly from `2s-1-2n` to `2s-1`. The top
  candidates `2n` and `2s-1` differ in parity, as do the bottom candidates `0`
  and `2s-1-2n`, so nothing cancels at either end. If `2s - 1 > 2n` the span
  is `2s - 1 >= 2n + 1`. Otherwise `2s <= 2n` and the span is
  `4n + 1 - 2s >= 2n + 1`.
- `c = mu z^(1-s) (B^2 + z^(2s-1) B^*2) / (B B^*)`. The numerator is coprime to
  `B` and to `B^*`, so `f1 = c f6 in R` forces `B B^* | f6`.
- `g = (w - 1)^2 / w = z^(1-2s) Delta^2 / (B B^*)^2`.

**Step 4: reduced equation.** Write `f6 = z^k B B^* psi` with `psi in R`. Here
`psi != 0` because `N6 = N2 != 0`. Then `f7^* f6 = e B B^* psi` and
`N6 = (B B^*)^2 psi psi^*`, so Step 2 becomes

    (*)  e B B^* (psi + psi^*) = z^(1-2s) Delta^2 psi psi^*.

**Step 5: reciprocal part.** Let `G = gcd(psi, psi^*)`. `G^*` is also a gcd of
the pair, so `G^* = u G` with `u = eps z^r` a unit. Write `psi = G psi2`. Then
`psi^* = u G psi2^*` and `gcd(psi2, psi2^*) = 1`. Dividing (*) by `G`:

    e B B^* L = u z^(1-2s) Delta^2 G psi2 psi2^*,   L = psi2 + u psi2^*.

- `psi2` divides `B B^* u psi2^*`, hence `B B^*`, and so does `psi2^*`. They
  are coprime, so `B B^* = psi2 psi2^* M` with `M in R`. So
  `2 span psi2 <= 2n`, that is `sigma := span psi2 <= n`.
- `e M L = u z^(1-2s) Delta^2 G`. `M` divides `B B^*` and is coprime to
  `Delta`, so `Delta^2 | L`. And `L != 0`, since `G != 0`.

**Step 6: Wronskian bound.** Put `Q = -eps z^r psi2^* / psi2`, so that
`L = psi2 (1 - Q)`, and

    theta Q / Q = W / (psi2 psi2^*),   W = r psi2 psi2^* + psi2 theta(psi2^*) - psi2^* theta(psi2).

Let `alpha in Kbar^x` be a zero of `Delta` of multiplicity `m`. Then
`psi2(alpha) != 0`, since otherwise `L(alpha) = 0` would force
`psi2^*(alpha) = 0` too, against `gcd(psi2, psi2^*) = 1`. So `Q(alpha) = 1`,
`psi2^*(alpha) != 0`, and `ord_alpha (1 - Q) = ord_alpha L >= 2m`. By
characteristic 0, `ord_alpha theta Q >= 2m - 1 >= m`. `W` has the same order at
`alpha` as `theta Q`, so `Delta | W`.

If the exponents of `psi2` lie in `[p, p + sigma]`, all four products in `W`
have exponents in `[-sigma, sigma]`. A nonzero `W` would then give
`span Delta <= span W <= 2 sigma <= 2n`, against Step 3. So `W = 0`,
`theta Q = 0`, `Q` is a constant `kappa` and `L = (1 - kappa) psi2`. Then
`span L <= n < 4n + 2 <= span Delta^2`, against `Delta^2 | L != 0`. So
`f2 != 0` is impossible.

QED

**Where characteristic `d` escapes.** Murray's Theorem 3 has `rho = z^t`, so
`B = 1`, `n = 0`, `s = t`, `Delta = 1 - z^(2t-1)`, `f7 = z^(2t-1)` and
`psi = z^(1-2t) (1 - z^(1-2t))^(d-2)`. Then `G = psi`, `psi2 = 1`,
`u = -z^((2t-1)d)` and `L = 1 - z^((2t-1)d) = (1 - z^(2t-1))^d`, which is
divisible by `Delta^2`. Here `W = r = (2t-1)d = 0` in `F_d` while `Q` is not
constant: both characteristic-0 facts about `theta` fail.
