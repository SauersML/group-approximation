---
rg: 2
id: bounded-degree-two-primitives-for-higher-rank-lattices
kind: claim
title: Operator-bounded degree-two primitives for Ad-modules of SL_N(Z), N at least 4
distinct_from:
  sln-z-flexibly-hs-stable: that is the stability conclusion; this is the single cohomological input from which the normalized-HS Newton iteration of `hs-stability-from-bounded-degree-two-primitives` derives it -- a statement about 2-cocycles, not about almost-representations.
  sl3z-regular-microstates-are-congruence-correctable: that is the rank-3 correctability hole attacked through extreme points; this is a rank-at-least-4 input living in degree-2 cohomology, where Bader--Sauer vanishing exists and SL_3 has none.
---

Claim.  Let `N >= 4`, `Gamma = SL_N(Z)`, and let `M` be a tracial
matrix ultraproduct with a unitary representation `pi` of `Gamma`
acting on `L^2(M)` by `Ad pi`.  There is a constant `C_N` such that
every 2-cocycle `c` of `Gamma` (on the cells of a fixed finite
presentation complex) with values in `M` which is a coboundary in
`L^2(M)` admits a primitive `y` (a 1-cochain with `delta y = c`)
satisfying BOTH

```text
|| y ||_2   <= C_N || c ||_2          (the usual modulus), and
|| y ||_op  <= C_N || c ||_op         (operator-norm control).
```

The first inequality is a quantitative form of Bader--Sauer's
property `(T_(N-2))` for the Ad-module (degree-2 gap); the second is
new and is the whole point.

## Attempts

- **Why degree one is free and degree two is not (the precise
  obstruction).**  In degree one, Kazhdan's argument produces the
  primitive of a 1-cocycle `b` as the fixed point of the affine
  isometric action, a 2-norm limit of Cesaro averages of the orbit
  points `b(g)`; since `|| b(g) ||_op <= 2` for cocycles coming from
  unitaries and the operator norm is lower semicontinuous on
  2-norm-bounded sets, the primitive is operator-bounded for free.
  In degree two the Hodge primitive `y = delta^* Delta_2^(-1) c` has
  no averaging structure: a Neumann-series inverse
  `Delta_2^(-1) = (1/mu) sum_n (1 - Delta_2/mu)^n` contracts in
  2-norm by `theta = 1 - lambda/mu` per term while its
  `l^1`-coefficient norm grows by `C = 1 + ||Delta_2||_(l^1)/mu`;
  truncating at `n ~ log(1/eps)` costs an operator-norm factor
  `eps^(-kappa)` with `kappa = log C / log(1/theta) ->
  ||Delta_2||_(l^1) / lambda >= 1`, independent of `mu`.  So the
  naive primitive is NOT operator-controlled, and this is exactly
  why no normalized-HS version of the De Chiffre--Glebsky--Lubotzky--
  Thom criterion is in the literature.  What would suffice: a
  positive-coefficient (averaging, `l^1`-norm one) expansion of the
  harmonic projection in degree two -- a Garland-type local-averaging
  formula -- or any SOS certificate for the degree-2 gap whose
  Neumann expansion has `kappa < 1`.
- **What is known on the gap side (source-verified earlier in the
  lane).**  Bader--Sauer [arXiv:2308.06517] give `(T_(N-2))` for
  `SL_N(Z)`, i.e. vanishing of (reduced) unitary cohomology through
  degree `N - 2`, so degree-2 vanishing holds for `N >= 4` and is
  sharp; the Kaluba--Mizerka--Nowak certified-SOS program supplies
  explicit degree-1 gaps at `SL_3` and is the natural source of an
  explicit degree-2 certificate at `SL_4` or `SL_5`.  The trivial-
  coefficient part is harmless: `H^2(SL_N(Z); C) = 0` for `N >= 3`
  (Borel stable range, Soule at `N = 3`).
- **Falsification gate.**  An Ad-module 2-cocycle of `SL_N(Z)` with
  `|| c ||_op <= 2`, 2-norm primitive, but no operator-bounded
  primitive would refute this claim; by the route it would have to
  arise from an almost-representation whose Newton correction is
  forced to be operator-large -- a structured non-stability
  phenomenon worth exhibiting in its own right.
