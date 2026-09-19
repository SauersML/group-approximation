---
rg: 2
id: fpbs-invariant-boundary-squares-need-heavy-returns
kind: claim
title: For a Gamma-invariant sigma-finite boundary measure lambda, the square return mass of each long group element is at most a product a_g b_g of a contracted and an expanded self-return of the two pieces, each with sphere sums at most M times the piece's mass; so a conservative square lambda x lambda needs heavy self-returns whose sphere maxima are non-summable for both pieces, which the shadow-product (Dini) count does not detect and the atomic loxodromic example shows is sharp
distinct_from:
  fpbs-finite-fibre-bb-classes-are-boundary-squares: that reduces finite-fibre BB certificates to the square problem (II_inf-square) and names the shadow-product count as the first test; this answers that test for invariant measures, replaces the shadow masses by self-return masses, and proves the resulting necessary condition.
  fpbs-dini-boundary-class-diagonal-dissipative: that bounds a return by the product of the shadow masses at g and g^{-1} for any quasi-invariant class; here invariance bounds it by self-return masses a_g <= lambda(A1 cap Sh(g^{-1})) and b_g <= lambda(A2 cap Sh(g)), and only the sphere maxima of these (not the full shadow-product sum) have to diverge.
  fpbs-rotation-boundary-class-refutes-shadow-summability: that shows shadow-product sums can diverge on quasi-invariant classes while the diagonal is still dissipative; this isolates, for invariant lambda, the quantity whose divergence is actually necessary.
---

**ESTABLISHED as an obstruction (necessary condition), not a resolution (written proof:
`research/fpbs-invariant-boundary-squares-need-heavy-returns-proof.md`).** The square problem (II_inf-square) of
`fpbs-finite-fibre-bb-classes-are-boundary-squares` stays OPEN. This node settles its "first test" and states where
every counting argument stops.

**Why this matters for the flagship.** For a cocompact lattice `Gamma < Sp(n,1)`, the finite-fibre half of the
Bevilacqua--Bowen route is equivalent to (II_inf-square): an ergodic, nonatomic, sigma-finite, `Gamma`-invariant
`lambda` on `dGamma` with `Gamma` conservative on `(d^2 Gamma, lambda x lambda)`. A "yes" gives fixed price one. The
only known filter was the shadow-product (Dini) count, which never used invariance. This node puts invariance into the
count.

## Setting

`Gamma` is nonelementary hyperbolic, with a `delta`-hyperbolic Cayley graph, `o = e`, spheres `S_n`, and thin shadows
`Sh_D(g) = {zeta : (zeta|g)_o >= |g| - D}`. `M = M(D, delta)` bounds the number of `g in S_n` whose shadow contains a
given point. `lambda` is `Gamma`-invariant and sigma-finite. `A1, A2` are Borel sets of finite positive measure with
disjoint closures `K1, K2`. The return sum of `E` is `R(E) = sum_g (lambda x lambda)(E cap g^{-1} E)`.

## Results

**Lemma 1 (two-sided North--South split).** There are `D` and `n_0`, depending on `d(K1,K2)` and `delta`, such that
if `(xi, eta) in K1 x K2`, `|g| >= n_0` and `(g xi, g eta) in K1 x K2`, then either
(i) `xi in Sh_D(g^{-1})` and `g eta in Sh_D(g)`, or (ii) `eta in Sh_D(g^{-1})` and `g xi in Sh_D(g)`.

**Theorem 2 (self-return factorisation).** Put
- `a_g = lambda(A1 cap g^{-1}A1 cap Sh_D(g^{-1}))` (the part of `A1` that `g` expands onto `A1`),
- `b_g = lambda(A2 cap g^{-1}(A2 cap Sh_D(g)))` (the part of `A2` that `g` contracts into `A2`),

and `a'_g`, `b'_g` with `A1`, `A2` exchanged. Then
`R(A1 x A2) <= C_0 + sum_{|g| >= n_0} (a_g b_g + a'_g b'_g)`, with `C_0 <= |B(n_0)| lambda(A1) lambda(A2)`.
Moreover, for every `n`,
`sum_{g in S_n} a_g <= M lambda(A1)` and `sum_{g in S_n} b_g <= M lambda(A2)`.
The second bound uses invariance: `b_g <= lambda(g^{-1}(A2 cap Sh_D(g))) = lambda(A2 cap Sh_D(g))`. For a merely
quasi-invariant class the expanded piece carries the Radon--Nikodym factor of `g^{-1}`, and this sphere bound fails.

**Theorem 3 (heavy returns are necessary).** Let `alpha_n = max_{S_n} a_g`, `beta_n = max_{S_n} b_g`, and define
`alpha'_n`, `beta'_n` likewise. Then
`R(A1 x A2) <= C_0 + M lambda(A1) sum_n beta_n + M lambda(A1) sum_n alpha'_n`, and also
`R(A1 x A2) <= C_0 + M lambda(A2) sum_n alpha_n + M lambda(A2) sum_n beta'_n`.
Hence, if `Gamma` is conservative on a positive-measure part of `A1 x A2`, then `sum_n beta_n + sum_n alpha'_n = infinity`
and `sum_n alpha_n + sum_n beta'_n = infinity`. In words: a conservative square needs group elements `g_n` of every
large length along which one piece contracts a non-summable amount of its own mass `c_n` into a shadow of radius
`~ e^{-epsilon n}`, and another piece expands mass `c_n` from such a shadow onto itself.

**Corollary 4 (consequences and calibration).**
1. *Recovers and sharpens Dini.* `a_g <= lambda(A1 cap Sh_D(g^{-1}))` and `b_g <= lambda(A2 cap Sh_D(g))`, so a piece
   whose shadow modulus is summable forces `R < infinity` (the Dini filter). The necessary condition of Theorem 3 is
   about self-returns, which are smaller.
2. *Nonatomic forces slow heavy returns.* If `lambda` is nonatomic, then `alpha_n, beta_n -> 0` (a sequence
   `beta_{n_k} >= c > 0` gives contracted masses `>= c` in shrinking shadows of `K2`, hence an atom). So the divergence
   in Theorem 3 must come from masses `c_n -> 0` with `sum c_n = infinity`, for example `c_n ~ 1/n`.
3. *Sharp on atoms.* For the counting measure on `Gamma h^+ ∪ Gamma h^-`, where `h^±` are the fixed points of a loxodromic `h`,
   `A1 = {h^+}` and `A2 = {h^-}` give `a_g = b_g = 1` along `g = h^{-k}`. The pair orbit is `Gamma/<h>` with counting
   measure, whose square part is conservative there. So the heavy-return condition cannot be weakened, and it is exactly
   the behaviour of a loxodromic pair that a nonatomic `lambda` would have to imitate at vanishing scales.
4. *Counting cannot finish the problem.* Theorem 2 gives each piece the same sphere-sum budget as a measure-preserving
   `Z`-action (where `sum_{|k| = n} m(A cap T^k A) <= 2 m(A)`). For `Z`-actions both answers occur: some infinite
   measure-preserving transformations have conservative Cartesian squares and some do not. So any argument that uses
   only the sphere sums and maxima of `a_g`, `b_g` cannot decide (II_inf-square). A kill must use how the heavy elements
   `g_n` are arranged in `Gamma`.

## What this leaves (named open statement)

- **(heavy-pair)** For a cocompact `Gamma < Sp(n,1)`: is there an ergodic, nonatomic, invariant `lambda` and pieces
  `A1, A2` with `sum_n sum_{g in S_n} a_g b_g = infinity`, that is, coincident heavy expanding and contracting
  self-returns along a single sequence of elements? Theorem 3 shows this is necessary for (II_inf-square). Corollary 4.3
  shows the loxodromic pair is its atomic model. The next test is whether the attracting points `g_n^+` of the heavy
  elements must converge, which would produce an atom and kill the class.
