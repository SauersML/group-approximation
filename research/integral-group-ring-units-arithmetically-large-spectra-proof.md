---
rg: 2
id: integral-group-ring-units-arithmetically-large-spectra-proof
kind: route
title: Finite spectrum of an integer Laurent polynomial in uu* gives a polynomial identity for uu*, which the domain property collapses to u = ±g
target: integral-group-ring-units-have-arithmetically-large-spectra
requires:
  - integral-spectra-of-small-capacity-are-finite
  - polya-integer-series-rational-off-small-capacity
  - elementary-amenable-torsion-free-strong-atiyah
---

Let `G` be a group with `C[G]` a domain, `u in Z[G]` a unit, `v = u^-1`,
`w = u u*`, `sigma = sigma(w)`, all in `C*_r(G)`. The canonical map
`C[G] -> C*_r(G)` is injective (the left regular representation is faithful on
`C[G]`), and the involution `*` preserves `Z[G]`.

**Step 1: the positive unit.**
- `u*` is a unit of `Z[G]` with inverse `v*`, so `w` is invertible in `Z[G]`
  with `w^-1 = (u*)^-1 u^-1 = v* v`.
- `w = u u* >= 0` and `w` is invertible, so `sigma ⊂ (0, infinity)`.
- `max sigma = ||u u*|| = ||u||^2 = b` and
  `min sigma = ||w^-1||^-1 = ||v* v||^-1 = ||v||^-2 = a`. The extreme points of
  the spectrum of a self-adjoint element lie in the spectrum.
- `tau(w) = sum_g u_g^2`, where `tau` reads the identity coefficient.

**Step 2: collapse lemma.** Let `f in Z[x, x^-1]` be nonconstant, and suppose
`cap(f(sigma)) < 1`. We show `u = +-g`.
1. `T = f(w)` lies in `Z[G]`, since `w^-1 in Z[G]`. `T` is self-adjoint because
   `w` and `w^-1` are self-adjoint and `f` has integer coefficients. By the
   spectral mapping theorem for continuous functions on `sigma ⊂ (0,infinity)`,
   `sigma(T) = f(sigma)`.
2. By `integral-spectra-of-small-capacity-are-finite` (case `n = 1`,
   `Z[G] ⊂ Z[i][G]`), `sigma(T)` is finite and `m(T) = 0` for a monic squarefree
   `m in Z[x]` of degree `d >= 1`.
3. `m(f(x))` is a nonzero Laurent polynomial: `f` is nonconstant and `m` is monic
   of degree `d`, so the extreme-degree term of `f^d` survives. Choose `N` with
   `p(x) = x^N m(f(x)) in Z[x]`. Then `p` is a nonzero polynomial and
   `p(w) = w^N m(T) = 0` in `C*_r(G)`, hence in `C[G]` by injectivity.
4. Factor `p(x) = c prod_j (x - mu_j)` with `c != 0` and `mu_j in C`. Then
   `prod_j (w - mu_j) = 0` in `C[G]`. Since `C[G]` has no zero divisors, some
   factor vanishes: `w = mu_j 1`.
5. `w in Z[G]` gives `mu_j = tau(w) in Z`, and `w^-1 in Z[G]` gives
   `1/mu_j in Z`, so `mu_j = +-1`. Also `tau(w) = sum u_g^2 > 0`, so `w = 1` and
   `sum_g u_g^2 = 1`. Hence `u` has a single nonzero coefficient, equal to
   `+-1`: `u = +-g`.

So for a unit `u` other than `+-g`, `cap(f(sigma)) >= 1` for every nonconstant
`f`. This is item 2.

**Step 3: items 3 and 4.** Capacity is monotone under inclusion, and a segment
of length `l` has capacity `l/4` (as recorded in
`polya-integer-series-rational-off-small-capacity`).
- `f = x`: `sigma ⊂ [a, b]`, so `1 <= cap(sigma) <= (b - a)/4`. Since `a > 0`,
  `||u||^2 = b >= 4 + a > 4`.
- `f = x^-1`: `sigma(w^-1) = sigma^-1 ⊂ [1/b, 1/a]`, so `1/a - 1/b >= 4` and
  `||v||^2 = 1/a >= 4 + 1/b > 4`.
- `f = x + x^-1`: `lambda + 1/lambda >= 2` on `(0, infinity)` and is maximized
  on `[a, b]` at an endpoint, and `a, b in sigma`. So `f(sigma) ⊂ [2, M]` with
  `M = max(a + 1/a, b + 1/b)`, and `1 <= (M - 2)/4` gives `M >= 6`. If
  `b + 1/b >= 6` then, as `b > 4`, `b >= 3 + 2 sqrt 2 = (1 + sqrt 2)^2`. If
  `a + 1/a >= 6` then, as `a < 1/4`, `1/a >= 3 + 2 sqrt 2`. Either way
  `max(||u||, ||v||) >= 1 + sqrt 2`.

**Step 4: the Promislow group.** `P` is torsion-free and virtually `Z^3`, hence
elementary amenable. By `elementary-amenable-torsion-free-strong-atiyah`, its
complex group algebra is a domain, so Steps 1--3 apply to every unit of `Z[P]`
other than `+-g`.

**Calibration of the hypothesis.** In `Z[C_5]`, with `s = x + x^-1` and
`t = x^2 + x^-2`: `s^2 = t + 2`, `t^2 = s + 2` and `s t = x^3 + x + x^-1 + x^-3
= s + t`. So `(s - 1)(t - 1) = s t - s - t + 1 = 1`, and `s - 1` is a unit other
than `+-g`. `C*_r(C_5) = C^5` gives `sigma(u u*)` finite, of capacity `0`. Step 2
breaks at item 4, because `C[C_5]` has zero divisors.

**Trust surface.**
- The two imported claims, as landed on main.
- Standard potential theory: monotonicity of logarithmic capacity under
  inclusion. It was not re-read at a primary source.
- Standard C*-algebra facts: the spectral mapping theorem and faithfulness of
  the left regular representation on `C[G]`.
