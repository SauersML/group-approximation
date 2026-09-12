---
rg: 2
id: monomial-crossed-product-dichotomy-proof
kind: route
title: Balance column weight against image multiplicity by Haar invariance, and turn each collision into an annihilator
target: monomial-crossed-product-elements-are-units-or-zero-divisors
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
  - odd-measure-space-has-no-honest-thompson-compression
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Theorem 3.1 of the artifact.

**Measure facts.**
- *Integrals agree.* `∫ c_x = sum_g lambda(supp b_g) = sum_g lambda(g supp b_g) = ∫ n_x`, because `V`
  preserves `lambda`.
- *Zero integrals.* `lambda` has full support on clopens, so a nonnegative locally constant function with
  integral `0` vanishes.

**Left side.**
- *(a) A zero column.* If `c_x = 0` on a clopen `W != ∅`, then `x 1_W = 0`.
- *(b) Cancellation-free.* If `c_x >= 1` everywhere and `n_x <= 1` everywhere, then `c_x = n_x = 1`.
- *(c) A collision.* If `c_x = 1` everywhere and `n_x(nu) >= 2`, take `g != g'` with `g^-1 nu` and
  `g'^-1 nu` in the respective supports, and put `k = g'^-1 g`. On a small clopen `W` the signs are
  constant, and `x 1_W = epsilon [g] 1_W = epsilon epsilon' x [k] 1_W`. So `x` kills
  `epsilon' 1_W - epsilon [k] 1_W`.
- *(d) A signed permutation.* If `c_x = n_x = 1`, then `x* x = x x* = eps_-`.

**Right side.** Apply the left side to `x*`, using `c_(x*) = n_x` and `n_(x*) = c_x`.
