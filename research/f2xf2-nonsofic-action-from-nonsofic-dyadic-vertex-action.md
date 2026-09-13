---
rg: 2
id: f2xf2-nonsofic-action-from-nonsofic-dyadic-vertex-action
kind: route
title: A nonsofic dyadic vertex action gives nonsofic frame dynamics of a lattice measure equivalent to F2 x F2
target: f2xf2-admits-nonsofic-action
requires:
  - dyadic-bruhat-tits-vertex-action-is-not-sofic
  - dyadic-vertex-soficity-equals-frame-dynamics-soficity
  - paunescu-class-is-measure-equivalence-invariant
---

Put `A = PSL_2(Z[1/2])`, `L = PSL_2(Q_2)`, `H = PSL_2(R) × L`, and fix a torsion-free cocompact
lattice `Λ <= L`.

1. By the required nonsoficity and item 3 ⇔ item 1 of
   `dyadic-vertex-soficity-equals-frame-dynamics-soficity`, the p.m.p. action `A ↷ (L/Λ, Haar)`
   is not sofic. It is essentially free, as checked in
   `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`, item 1. So `A ∉ 𝒮`.
2. `A` and `Γ(2) × Λ ≅ F_2 × F_r` are lattices in `H`, and `F_2 × F_r` has finite index in
   `F_2 × F_2`. This is item 1 of the route `dyadic-vertex-action-sofic-from-f2xf2-paunescu-class`.
   So `A` is measure equivalent to `F_2 × F_2`.
3. By `paunescu-class-is-measure-equivalence-invariant`, `F_2 × F_2 ∉ 𝒮`. Its explicit transfer
   produces the essentially free nonsofic action of `F_2 × F_2` on `(Ω × (L/Λ) × B)/A`, where `Ω`
   is a coupling and `B` a Bernoulli shift of `A × F_2 × F_2`. That is the target.
