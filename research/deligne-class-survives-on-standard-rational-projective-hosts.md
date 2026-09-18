---
rg: 2
id: deligne-class-survives-on-standard-rational-projective-hosts
kind: claim
title: Deligne's class never dies over the rational Cantorization of a representation sphere of Sp_2n(Z) with a positive-measure orbit whose stabilizer contains a symplectic block; in particular not for the standard representation
distinct_from:
  groupoid-lifts-of-central-extensions-need-no-invariant-measure: that needs an invariant probability measure, which boundary-type actions lack; this uses only the Lebesgue measure class, through Mackey-Moore induction, and applies to actions with no invariant measure.
  deligne-class-dies-on-some-rational-projective-host: that is the open positive question; this closes its most natural instance, the standard embedding Sp_2n(Z) <= GL_2n(Z) <= T_(2n-1).
  deligne-lift-actions-are-not-almost-v: that excludes one finiteness engine for Lagrangian hosts; this excludes the lift itself over representation-sphere hosts.
---

**ESTABLISHED** (lane proof, modulo textbook inputs flagged below; not reviewed).

## Statement

Let `n ≥ 2`, `G = Sp_{2n}(R)`, `Γ = Sp_{2n}(Z)`. Let `ρ : Sp_{2n} → GL_N` be a rational
representation with `ρ(Γ) ≤ GL_N(Z)`, acting on the ray sphere `S^{N−1}`. Suppose some
`G`-orbit `O ⊆ S^{N−1}` has positive Lebesgue measure, and its point stabilizer `H`
contains a standard block `Sp(W)(R)`: `W ⊆ R^{2n}` symplectic of dimension `≥ 2`,
acting trivially on `W^⊥`.

Let `Y` be a Cantor `Γ`-space with an equivariant continuous `π : Y → S^{N−1}` that is
injective over a `Γ`-invariant Borel set `E` of full measure, with Borel inverse on
`E`. Then Deligne's class `[ε] ∈ H^2(Γ; Z)` (of the preimage of `Γ` in the universal
cover of `G`) does **not** die in `H^2(Γ; C(Y, Z))`. So Deligne's lattice has no lift
over `Y` in the sense of `central-extension-shear-lift-into-rational-projective-groups`.

**Instances.**
1. `ρ` standard (`N = 2n`), `Y = Ŝ_{2n−1}`: here `G` is transitive on `S^{2n−1}`, and
   `H = Stab(v)` contains `Sp(W)` for `W` the symplectic complement of a plane
   through `v`. The fibres of `Ŝ_{2n−1} → S^{2n−1}` are single points over rays lying
   on no rational hyperplane, a full-measure invariant set. So the standard embedding
   `Γ ≤ GL_{2n}(Z) ≤ 𝒯_{2n−1}` carries no lift.
2. `n = 2`, `ρ = Λ^2_0` (the 5-dimensional representation, `Sp_4 = Spin(2,3)`): the
   open orbit of `ω_1 − ω_2` (for a splitting `W_1 ⊕ W_2`) has stabilizer containing
   `Sp(W_1) × Sp(W_2)`. So no lift here either, although the complementary open
   region of anti-de Sitter type has stabilizer `Spin(1,3)` and passes the test.

## Proof

Suppose `[ε]` dies on `Γ ⋉ Y`, with locally constant `k`. Composing with `π^{-1}` on
`E ∩ O` gives a bounded Borel `κ` on `Γ × O` with `d·ε = δκ` almost everywhere. So
`[ε] ↦ 0` in `H^2(Γ; L^∞(O, R))`, where `O = G/H`. Then:
- **Shapiro.** By the Mackey–Moore induction isomorphism (Moore; Zimmer, *Ergodic
  Theory and Semisimple Groups*; textbook, not read at source),
  `H^2(Γ; L^∞(G/H, R)) ≅ H^2_m(H; L^∞(Γ\G, R))`, and the restriction of the `G`-class
  corresponds to its restriction to `H`, with constant coefficients.
- **Integration.** Integrating against the `G`-invariant probability measure on `Γ\G`
  is an `H`-map `L^∞(Γ\G, R) → R`. It sends the class to `res^G_H [ε_G]_R`, which
  must therefore vanish in `H^2_m(H; R) = H^2_c(H; R)` (Wigner).
- **Restriction to the block.** Restrict further to `Sp(W)(R) ≤ H`. The inclusion
  `Sp(W) ⊂ Sp_{2n}` is an isomorphism on `π_1 ≅ Z`, so the restricted class is the
  universal-cover class of `Sp(W)(R)`. Its real image is a nonzero multiple of the
  Kähler class, which is nonzero in `H^2_c(Sp(W)(R); R) ≅ R` (Guichardet–Wigner;
  textbook). Contradiction. ∎

## Reading

Over representation spheres, the lift needs `ρ` whose generic stabilizers carry no
Hermitian block. Direct sums `k·std` with `k ≥ 2n` have trivial generic stabilizer,
so this obstruction does not fire for them
(`deligne-class-dies-on-some-rational-projective-host`).
