---
rg: 2
id: vertex-rounding-alone-normalizes-each-theorem-e-model
kind: claim
title: At the Theorem E pair, vertex rounding of one model normalizes that model, so no liftable masa of the actor commutant is ever consumed
distinct_from:
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open statement that every model rounds to unit type; this is the per-model implication from vertex rounding to normalization, composed from the established root-mass claims.
  hs-vertex-rounding-and-liftable-masa-force-normalization: that derives normalization from vertex rounding together with a liftable masa, for any infranormal Kazhdan pair; this derives it from vertex rounding alone at the Theorem E pair, which makes the masa input redundant there.
  unit-type-vertex-rounding-forces-compressor-commutant-rigidity: that assumes the rounding is of unit type; this assumes only vertex rounding and gets unit type from the shallow and deep root-mass theorems.
artifacts:
  - research/artifacts/hs-masa-lift-positive-part2-2026-09-13.md
---

**ESTABLISHED** (given the four premises of its route, all established on main). Let
`Gamma = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(+-1)]) x| SL_d(Z)`, with `r, d >= 3`. Let
`sigma : G -> U(prod_U M_n)` be trace-preserving and satisfy (H1) for this model: after `o(n)`
padding there are genuine `pi_n : Gamma -> U(n')`, `n'/n -> 1`, with
`max_(s in F) ||sigma_n(s) - pi_n(s)||_2 -> 0`. Then:

- the rounding is of unit type, `tau(1 - P_n) -> 0` along `U`;
- `sigma(G)` normalizes `sigma(Gamma)' cap prod_U M_n`;
- `alpha = Ad sigma|_(sigma(Gamma)' cap M)` factors through `G / <<Gamma>> = SL_d(Z)`. So the actor
  commutant is the fixed-point algebra of an `SL_d(Z)`-action on `prod_U pi_n(Gamma)'`.

**Consequences.**
- `hs-vertex-rounding-and-liftable-masa-force-normalization` is dominated at this pair, and the
  route `hs-normalization-via-vertex-rounding-and-liftable-masa` consumes
  `actor-commutant-has-liftable-masa-in-every-model` for nothing.
- For `non-hyperlinear-group`, only trace-preserving models (`tau o sigma = delta_e`) matter:
  a hyperlinear embedding of the wreath restricts to one. So the route
  `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding` already needs only (H1) at such models,
  and a liftable masa adds nothing on the way to `non-hyperlinear-group`.
- **Scope.** The uniform inequality `hs-uniform-compression-stability-at-the-theorem-e-pair` is
  equivalent to normalization for every homomorphism, with any trace
  (`kazhdan-commutant-compression-stability-is-finitary`). The root-mass premises are stated for
  trace-preserving models. So this claim gives that inequality from (H1) only at models whose trace
  those premises cover. Extending them to arbitrary traces is not checked here.
- In the three-faces readoff of `research/artifacts/unified-compression-rigidity-2026-09-12.md`, the
  localization face at this pair is supplied by the Laurent torus (shallow mass) and the compressor
  attractors (deep mass) once rounding holds, not by a masa.

Derivation: `vertex-rounding-alone-normalizes-theorem-e-model-proof`. Artifact part 2, Sections
1-3.
