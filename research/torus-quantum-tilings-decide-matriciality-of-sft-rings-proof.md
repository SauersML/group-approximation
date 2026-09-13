---
rg: 2
id: torus-quantum-tilings-decide-matriciality-of-sft-rings-proof
kind: route
title: Induce covariant families from torus modules, restrict periodic families to their torus, and specialize exact models to characteristic p
target: torus-quantum-tilings-decide-matriciality-of-sft-rings
requires: [matricial-z2-sft-crossed-products-give-quantum-tilings, matricial-aperiodic-sft-rings-are-not-quantum-rigid]
artifacts:
  - research/artifacts/un-labbe-ring-torus-tilings-2026-09-13.md
---

Artifact §2, Theorem 1.

**Induction** (torus module ⇒ covariant family).
- Put `W = ⊕_(s ∈ T_Λ) V` and `(U^g ξ)_s = ξ_(s+g)`. `E_a(z)` acts on summand `s` as `e_a(z̄ + s)`.
- Then `U^g E_a(0) U^(-g) = E_a(g)`, and `U_1, U_2` commute with finite order.
- (Q1) is (T1). If `|z - z'| <= 2D`, the classes differ by a representative in `B_(2D)`, so (T2) gives (Q2). (Q3)
  is (T3).

**Restriction** (covariant family over a finite field ⇒ torus module).
- `Λ = ker(g ↦ U^g)` has finite index. `E_a(z + λ) = E_a(z)`, so `e_a(t) := E_a(z)` for `z ∈ t` is well defined.
- (T1)–(T3) follow from (Q1)–(Q3), choosing representatives within `B_(2D)` for (T2).

**Specialization** (exact matricial ⇒ families over `k`). By item 1 of
`matricial-aperiodic-sft-rings-are-not-quantum-rigid`, the scale-`D` identities are finitely many polynomial
identities with `F_p` coefficients. An exact model supplies a point of their variety in characteristic `p`, hence
a point over a finite field containing `k`. Restricting scalars gives a family over `k`.

**Equivalence.**
- (⇒) Specialize, then restrict.
- (⇐) Induce at every scale. The families-to-matricial direction of
  `matricial-z2-sft-crossed-products-give-quantum-tilings` gives the embedding: the colimit of local presentations,
  simplicity of `R` for free minimal `Ω`, and `simple-rings-with-local-matrix-models-are-matricial`.
