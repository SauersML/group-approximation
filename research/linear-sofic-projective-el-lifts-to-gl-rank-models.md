---
rg: 2
id: linear-sofic-projective-el-lifts-to-gl-rank-models
kind: claim
title: A linear sofic projective elementary group lifts to an exact general-linear rank model whose kernel is exactly the scalar subgroup
distinct_from:
  rank-modelled-simple-rings-give-linear-sofic-projective-el: that goes from a ring rank model to a group model through the same adjoint computation; this goes from a projective group model to a general-linear group model of EL_N itself, with no ring input.
  linear-sofic-el-groups-force-rank-model: that is the open converse (Σ⇒); this reduces it to ring rigidity of exact general-linear rank models of EL_N(R) with kernel exactly the scalars.
artifacts:
  - research/artifacts/un-sigma-converse-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a perfect field (for instance a finite field), `R` a unital
`k`-algebra, `N >= 2`,
`Z_N = EL_N(R) ∩ k^x 1_N`, and `S_N = EL_N(R)/Z_N`. Suppose `S_N` is `k`-linear sofic in the
ultraproduct sense: there is an injective homomorphism

```text
iota : S_N -> P = prod_omega PGL_(n_i)(k) / d,   d((A_i),(B_i)) = lim_omega min_(λ ∈ k^x) rk(A_i − λ B_i)/n_i.
```

Then there is a homomorphism

```text
sigma : EL_N(R) -> U = prod_omega GL_(n_i^2)(k) / d_rank,     ker sigma = Z_N exactly.
```

`sigma` is `Ad ∘ iota ∘ quotient`, with `Ad(A) = A ⊗ (A^(-1))^T`.

**Consequence.** Rung (Σ⇒) `linear-sofic-el-groups-force-rank-model` follows from the ring
rigidity statement: every homomorphism `EL_N(R) -> U` (a general-linear rank ultraproduct over
`k`) with kernel exactly `Z_N`, for all `N >= 2`, forces a unital rank model of `R` over `k`.
No metric stability input is needed at this rung: linear soficity is already an exact
homomorphism into an ultraproduct, so all Steinberg relators hold exactly in `U`. The gap is
algebraic (artifact §2).

Route: `linear-sofic-projective-el-lifts-to-gl-rank-models-proof`.
