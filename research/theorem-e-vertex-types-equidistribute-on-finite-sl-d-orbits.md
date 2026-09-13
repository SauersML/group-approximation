---
rg: 2
id: theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits
kind: claim
title: Under vertex rounding at the Theorem E pair, vertex types move by a genuine SL_d(Z)-action with finite orbits, their mass equidistributes on orbits, and the central fixed algebra lifts to orbit partitions
distinct_from:
  amenable-type-cycle-kills-liftable-masas: that shows a long cycle of central types under one compressor, with no Kazhdan group acting on types, leaves no liftable masa; this proves that at the Theorem E pair under vertex rounding the whole actor quotient SL_d(Z) acts on types by a genuine action, so property (T) excludes that mechanism and the central part of the actor commutant lifts.
  compressor-cycles-block-central-projection-rounding: that shows central projections almost invariant under the single unipotent compressor need not round in congruence representations; this uses almost invariance under a Kazhdan generating set of SL_d(Z), which forces orbit-constancy on l^2 of the type set.
  vertex-rounding-alone-normalizes-each-theorem-e-model: that gives unit type and normalization from vertex rounding for one model; this describes the type dynamics of the normalized action and lifts the center-valued part of the actor commutant.
artifacts:
  - research/artifacts/hs-masa-lift-positive-part3-2026-09-13.md
---

**ESTABLISHED** (given the premises of its route). Let
`Gamma = EL_r(F_q[x_1..x_d]) < G = EL_r(L) x| SL_d(Z)`, with `L = F_q[x^(+-1)]` and `r, d >= 3`. Let
`sigma : G -> U(prod_U M_n)` be trace-preserving with (H1) roundings `pi_n`. Write:
- `A_n = pi_n(Gamma)'`, with types `rho` given by the minimal central projections `z_rho`;
- `p_n(rho) = tau(z_rho)`, and `Q = sigma(G)' cap prod_U M_n`;
- `X` for the irreducible representations of `St_r(L)` with finite unit-type image, on which
  `SL_d(Z)` acts genuinely through `x^v -> x^(Mv)`.

Then, along `U`:
1. **Types.** Off trace `-> 0`, the types of `pi_n` are points of `X`. Every `SL_d(Z)`-orbit in `X` is
   finite: a type of level `m` factors through `St_r(F_q[(Z/m)^d])`, and the action factors through
   `SL_d(Z/m)`.
2. **Genuine dynamics.** `Ad sigma(M)` acts on the center-valued observables `prod_U Z(A_n)` by
   `g -> g o M^(-1)` for the genuine action on types, uniformly over contractions. Hence
   `||M_* p_n - p_n||_1 -> 0` for every `M in SL_d(Z)`.
3. **Equidistribution.** `sqrt(p_n)` is asymptotically orbit-constant in `l^2(X)`. So the type mass is
   asymptotically uniform on `SL_d(Z)`-orbits.
4. **Central lift.** The orbit projections `e_O = sum_(rho in O) z_rho`, plus one block of vanishing
   trace, have vanishing summed boundary, and `Q cap prod_U Z(A_n) = prod_U span{e_O}`.
5. **Multiplicity-free (LM).** If the rounding is asymptotically multiplicity-free,
   `lim_U tau(sum_(m_rho >= 2) z_rho) = 0`, then `Q` is this abelian ultraproduct of partition
   algebras. So `actor-commutant-has-liftable-masa-in-every-model` holds for `sigma`.

**Reading.**
- The type-cycle obstruction cannot occur at this pair under vertex rounding. Property (T) of the
  actor quotient `SL_d(Z)`, acting genuinely on unit-type types, is Kun's lemma on types, with
  orbits as components.
- What (LM) still asks here sits in the multiplicity fibres. On an orbit of level `m`, the fixed
  algebra is the relative commutant of the holonomy on the multiplicity space. That holonomy is an
  almost projective representation of a Kazhdan stabilizer containing the congruence subgroup
  `SL_d(Z)(m)`: a `DEC`-type problem for finite-index subgroups of `SL_d(Z)`, recorded as a reading,
  not a claim.
- Nothing here is consumed by `non-hyperlinear-group` (see
  `vertex-rounding-alone-normalizes-each-theorem-e-model`).

Derivation: `theorem-e-vertex-types-equidistribute-proof`. Artifact part 3, Sections 1-4.
