---
rg: 2
id: kazhdan-cover-actor-models-normalize-vertex-commutants
kind: claim
title: Models pulled back from genuine representations of a cover with a compressed Kazhdan lift of the vertex normalize the vertex commutant
distinct_from:
  commutant-no-growth: that is the exact dimension count for one genuine finite-dimensional representation of the group; this runs it at the finite stages of a cover and adds the Kazhdan identification of the ultraproduct commutant, for models that are not representations of the group.
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that decides when a pulled-back vertex model rounds, by the kernel's fixed mass; this proves the pulled-back actor model normalizes the vertex commutant whether or not the vertex rounds.
  unit-type-vertex-rounding-forces-compressor-commutant-rigidity: that derives normalization from rounding of the vertex plus vanishing non-unit mass; this assumes no rounding, only genuine representations of a compressor-compatible Kazhdan cover.
  hyperlinear-group-carries-nontrivial-rigid-defect: that asks for a hyperlinear witness with a nontrivial rigid defect; this excludes one family of models as a source of the non-normalized commutant the witness construction needs.
artifacts:
  - research/artifacts/hl-nh-el3-compressor-2026-09-14.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `P : Ĝ -> G` is a surjective homomorphism with kernel `N`, and `Γ <= G`.
- `Γ̂ <= Ĝ` has property (T), and `P(Γ̂) = Γ`.
- `T̂ ⊆ Ĝ` satisfies `t Γ̂ t^-1 <= Γ̂` for every `t ∈ T̂`, and `G = <Γ ∪ P(T̂)>`.
- `U` is a free ultrafilter, `ρ_n : Ĝ -> U(d_n)` are unitary representations, and
  `M = prod_U M_(d_n)` carries the normalized traces. The kernel acts trivially in the limit:

  ```text
  lim_U ||ρ_n(m) - 1||_2 = 0     for every m ∈ N.                              (KC)
  ```

**Theorem.**
1. `σ(g) = [ρ_n(ĝ)]_U`, for any `ĝ ∈ P^-1(g)`, is a well-defined homomorphism `σ : G -> U(M)`.
2. `σ(Γ)' ∩ M = prod_U A_n`, where `A_n = ρ_n(Γ̂)' ∩ M_(d_n)` is the exact commutant.
3. `σ(G)` normalizes `σ(Γ)' ∩ M`.

No trace preservation and no infranormality are assumed.

**Reading.**
- **Old special case.** `N = 1` recovers the recorded fact that ultraproducts of genuine
  finite-dimensional representations of `G` normalize.
- **Where the content is.** Every homomorphism `G -> U(M)` is pulled back from genuine
  representations of a free group on generators of `G`, and (KC) then holds automatically. The
  preimage of `Γ` in a free group is free and has no property (T). So the Kazhdan hypothesis on the
  lift `Γ̂` carries the whole theorem.
- **Finite-dimensional stages are load-bearing.** For a genuine representation into a II₁ factor the
  conclusion fails: `G` acting on the wreath factor `L(W)` has a non-normalized vertex commutant
  (`kun-thom-wreath-factor-is-exact-nonnormalized-commutant`).
- **Non-roundable vertices allowed.** By `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` the
  vertex restriction of such a model rounds exactly when the fixed mass of `N ∩ Γ̂` tends to one.
  When it does not, the vertex is not flexibly roundable, and the commutant is still normalized. So
  non-roundability of the vertex is necessary for a wall but not sufficient.
- **Diffuse commutants allowed.** `prod_U A_n` is diffuse whenever the dimensions of the `A_n` grow;
  compressors still act on it as automorphisms.

Derivation: `kazhdan-cover-actor-models-normalize-proof`.
