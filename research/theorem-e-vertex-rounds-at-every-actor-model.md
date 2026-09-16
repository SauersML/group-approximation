---
rg: 2
id: theorem-e-vertex-rounds-at-every-actor-model
kind: claim
title: Every trace-preserving model of the Theorem E actor rounds flexibly on the polynomial vertex
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1) over every infranormal, non-normal Kazhdan pair, refuted at a product pair with an affine symplectic factor; this is (H1) at the Theorem E pair only, which that refutation does not touch.
  theorem-e-vertex-rounds-to-unit-type-representations: that asks for roundings of unit type; this asks only for some genuine rounding, which that claim strengthens.
  vertex-rounding-with-log-depth-rate: that is (H1) with a quantitative rate against the maximal non-unit depth; this is (H1) with no rate.
  kt-actor-model-with-totally-non-roundable-vertex: that asks for one totally non-roundable actor model at some parameter with gcd(r, q-1) = 1; this asserts rounding at every model and every parameter, so it refutes that claim.
  laurent-vertex-rounds-for-every-model: that rounds on the Laurent vertex EL_r(F_q[x^(±1)]); this rounds on the polynomial vertex EL_r(F_q[x_1..x_d]).
  vertex-rounding-fails-at-symplectic-product-pair: that is the counterexample at the product with Z^2g x| Sp_2g(Z); this is the Theorem E vertex itself, which has no such factor and finite H_1 and, in the stable range, finite H_2.
---

**OPEN.** Let `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x_1^(±1)..x_d^(±1)]) ⋊ SL_d(Z)`, with `q` a prime power
and `r, d >= 3`, be the Kun--Thom Theorem E pair, and let `F_Γ` be a finite generating set of `Γ`. For every
trace-preserving `σ : G -> U(prod_U M_n)`, with coordinates `σ_n`, after `o(n)` padding there are genuine
representations `π_n : Γ -> U(n')`, `n'/n -> 1`, with

```text
max_(s in F_Γ) ||σ_n(s) - π_n(s)||_2  ->  0   along U.
```

This is hypothesis (H1) of `hs-rounding-and-actor-gap-force-ccr` at the Theorem E pair, for every model. It
replaces `hs-stable-vertex-rounding-for-every-model` as the rounding premise of the Theorem E chain.
- Its general form is false (`vertex-rounding-fails-at-symplectic-product-pair`).
- Every Theorem E attempt recorded on that node applies here unchanged.
- Propagation along words shows the choice of `F_Γ` does not matter.

## Attempts

- **Inherited (2026-09-12 to 2026-09-13).** The attempts recorded on `hs-stable-vertex-rounding-for-every-model`
  were all made at the Theorem E pair.
  - Literal commutant rounding is dead (`hs-literal-commutant-profile-rounding-is-false`).
  - The robust spectral gap supplies no genuine representation (`el-r-polynomial-robust-spectral-gap`).
  - Uniform Kazhdan constants are unavailable (`uniform-kazhdan-fails-for-linear-theorem-e-pair`).
  - Congruence-kernel projections vanish at every fixed level
    (`theorem-e-congruence-projections-vanish-at-regular-trace`).
  - The roundable corner is actor-invariant, so (H1) is zero-one after an actor-invariant split
    (`compressor-extension-makes-roundable-vertex-part-invariant`). Wreath models are totally non-roundable
    (`kt-wreath-models-never-round-on-the-vertex`).
  - Retract witnesses do not extend to the actor (`el-r-polynomial-vertex-not-flexibly-hs-stable`).
- **Transfer of the product-pair counterexample (2026-09-16, lane
  `swarm-hs-stable-vertex-rounding-for-every-model`).** It does not transfer.
  - The counterexample needs a Kazhdan direct factor of the vertex whose trace-preserving models stay
    non-roundable after amplification. For `Z^(2g) ⋊ Sp_(2g)(Z)` these come from a non-torsion class in `H^2`
    and property (T) of the Heisenberg cover.
  - `Γ` has finite `H_1`, and in the stable range `r >= d + 3` it has `H_2(Γ; Z) = 0` (van der Kallen and
    Quillen imports, unverified; see `kt-actor-model-with-totally-non-roundable-vertex`). So scalar cocycle
    models of `Γ` round strictly (`finite-multiplier-projective-models-round-strictly`).
  - A witness here needs non-scalar defects, and it must extend to the actor.
  - **Where it dies.** No non-scalar amplification-robust obstruction is known for `EL_r` over polynomial rings.
