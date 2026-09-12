---
rg: 2
id: vertex-rounding-non-unit-mass-at-origin
kind: claim
title: Under vertex rounding, non-unit congruence mass sits at the origin place and must spread over many depth scales
distinct_from:
  unit-type-vertex-rounding-forces-compressor-commutant-rigidity: that bounds the commutant excess by the total non-unit mass; this locates the non-unit mass, excluding intermediate places and single-scale origin depth profiles, by matching two roundings of the compressed vertex.
  theorem-e-vertex-rounds-to-unit-type-representations: that asks for vanishing non-unit mass; this proves the part of it at intermediate places and at fixed finite quotients, and a depth-scale bound at the origin, leaving evaluation-at-origin factors and many-scale origin profiles open.
  ccr-under-vertex-rounding-from-few-aspect-scales: that bounds the commutant excess by the number of occupied aspect-ratio scales; this bounds origin congruence mass by the number of occupied nilpotency-depth scales.
artifacts:
  - research/artifacts/nh-unit-type-counterexample-2026-09-12.md
---

**ESTABLISHED.** Let `R_+ = F_q[x_1..x_d]` and `Γ = EL_r(R_+) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`,
with `r, d >= 3`. Let `σ : G -> U(prod_U M_n)` be trace-preserving and satisfy (H1), with rounding
representations `π_n` of `Γ`.

For an irreducible constituent `ρ` of `π_n`:
- **kernel ideal:** `J_ρ = {a : ρ(e_ij(a)) = 1 for all i ≠ j}`;
- **type** of a maximal ideal `m` of `R_+/J_ρ`: `S(m) = {i : x_i ∈ m}`. A place is *intermediate*
  if `∅ ≠ S(m) ≠ {1..d}`, and the *origin* is `m_0 = (x_1..x_d)`;
- **depth:** `o_j` is the nilpotency order of `x_j` in the origin factor.

Fix `A ∈ SL_d(Z)` with every entry `>= 1`, and let `η_n -> 0` measure the distance between the two
roundings of `Λ = AΓA^(-1)` in the proof. Then:

1. **Intermediate places.** The trace of the constituents with an intermediate local factor is at
   most `12 η_n`, so it tends to `0`.
2. **Depth scales.** If `A_jj >= 2` and `P_n(t)` is the mass of constituents whose origin factor has
   `o_j >= t`, then `P_n(t) <= P_n(2t-1) + 24η_n` for all `t >= 1`. Hence, for `t >= 2`,
   `P_n(t) <= 24η_n (log_(3/2)(D_n/t) + 2)`, where `D_n` is the largest origin depth.
3. **Fixed quotients.** For every fixed finite-index ideal `I`, the mass of constituents factoring
   through `St_r(R_+/I)` tends to `0`.

**Reading for the counterexample side.**
- A model refuting unit-type rounding cannot put order-one mass at intermediate places. That rules
  out truncations in some but not all variables, and any fixed finite quotient.
- Deep origin mass needs `η_n log D_n` bounded below, i.e. a depth profile spread over at least order
  `1/η_n` dyadic scales in every direction.
- Otherwise the non-unit mass sits on evaluation-at-origin factors tensored with unit-type factors
  at growing levels. That is the smallest shape this claim leaves open.

No root is affected. Derivation: `vertex-rounding-origin-mass-proof`.
