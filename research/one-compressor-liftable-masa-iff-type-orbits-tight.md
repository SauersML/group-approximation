---
rg: 2
id: one-compressor-liftable-masa-iff-type-orbits-tight
kind: claim
title: The fixed algebra of one type-permuting compressor has a liftable masa exactly when no type mass escapes to infinite period
distinct_from:
  amenable-type-cycle-kills-liftable-masas: that is the single long cycle with a quantitative character estimate; this is the exact criterion for an arbitrary permutation of types, in both directions, including the construction of the masa when periods are tight.
  theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits: that lifts the central part of the full actor commutant at the Theorem E pair through property (T) of SL_d(Z) acting on types; this treats one compressor, an amenable Z-action on types, where tightness of periods replaces expansion.
  hs-block-gap-iff-liftable-masa-of-actor-commutant: that characterizes liftable masas by a summed Kazhdan gap for Kazhdan actors; this characterizes them for a single compressor by a dynamical condition on central types, with no gap.
---

**ESTABLISHED.** Let `U` be a free ultrafilter and `M = prod_U M_(N_n)`. For each `n` let:
- `A_n <= M_(N_n)` be a unital `*`-subalgebra with minimal central projections `e_x`, `x in X_n`, so
  each `A_x = A_n e_x` is a factor;
- `V_n` be a unitary with `V_n A_n V_n^* = A_n`, so `V_n e_x V_n^* = e_(beta_n(x))` for a permutation
  `beta_n` of `X_n`.

Put `A = prod_U A_n`, `V = [V_n]`, `Q = {V}' cap A`. For an orbit `O` of `beta_n` write `l(O)` for
its length and `P_(n,>K)` for the sum of `e_x` over orbits of length `> K`. Say the periods are
**tight** if

```text
lim_(K -> infinity)  lim_U  tau( P_(n,>K) )  =  0 .
```

**Theorem.** `Q` has a maximal abelian subalgebra of the form `prod_U C_n`, with `C_n` spanned by a
finite partition of unity of `M_(N_n)` by projections, **if and only if** the periods are tight.

1. **Tight gives a masa.** On each orbit `O` with base point `x`, `Ad V_n^(l(O))` restricts to an
   inner automorphism `Ad w_x` of the factor `A_x`. Choose a masa `D_x` of `A_x` containing `w_x`, and
   put `q_p = sum_(k < l(O)) V_n^k p V_n^(-k)` for the minimal projections `p` of `D_x`. The `q_p` form
   a partition of unity commuting exactly with `V_n`, and `prod_U span{q_p}` is maximal abelian in
   `Q`. The maximality step is the spectral gap `16 / l^2` of the `l`-cycle.
2. **Escaping mass kills every masa.** If `delta = lim_K lim_U tau(P_(n,>K)) > 0`, then for every
   liftable abelian `C <= Q` there is a central contraction
   `f = sum_(l(O) > K_n) sum_(k < l(O)) exp(2 pi i theta_n k) e_(beta^k x_O)` in `Z(Q)` with
   `lim_U ||f - E_C f||_2^2 >= delta / 2`. Here `K_n -> infinity` keeps half of the escaping mass,
   and `theta_n -> 0` sits above the summed boundary of `C`.

**Realization.** For `Gamma` Kazhdan and genuine representations of `Gamma x|_alpha Z` whose restriction
to `Gamma` has types `rho` permuted by `rho -> rho o alpha^(-1)`, `Q` is the relative commutant of the
image (`at-op62-holds-for-representation-lifts`). So such an ultraproduct lifts a masa of its
relative commutant iff the `alpha`-periods of its types, weighted by trace, are tight.

## Reading

- **Why (T) of the actor is spent on types.** One compressor generates an amenable action on types.
  There the masa lifts only when periods stay bounded on most of the mass. At the Theorem E pair,
  vertex rounding forces the type mass to unbounded congruence level (item 3 of
  `vertex-rounding-non-unit-mass-at-origin`), and nothing there keeps the period of one compressor
  bounded. The full actor `SL_d(Z)` needs no such bound, because it expands on orbits
  (`theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits`).
- **Holonomy is free for one compressor.** The multiplicity fibres never obstruct in this setting: the
  holonomy of one orbit is a single unitary `w_x`, and its eigenbasis lifts. So for one compressor the
  whole content of (LM) is the period distribution. For a Kazhdan actor the fibre holonomy is an
  almost representation of a stabilizer, and that is where the remaining content of
  `actor-commutant-has-liftable-masa-in-every-model` sits.
- **Not claimed.** The approximate transcription to one compressor of a Theorem E model, where
  `Ad sigma_n(A)` permutes types only up to vanishing error, is not written here. The non-liftability
  direction survives such errors in the same proof. The masa construction needs an exactly
  normalizing unitary.

Derivation: `one-compressor-liftable-masa-iff-type-orbits-tight-proof`.
