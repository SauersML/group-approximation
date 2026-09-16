---
rg: 2
id: kt-genuine-atomic-vertex-coordinate-models-normalize
kind: claim
title: Ultraproduct models of the Theorem E actor with genuine atomic vertex coordinates normalize the vertex commutant, with no trace condition
distinct_from:
  ccr-holds-for-all-genuine-fd-coordinate-models: that needs genuine finite-dimensional representations of all of G in matrix coordinates; this allows arbitrary Connes-embeddable II_1 coordinates, where only the vertex coordinates are genuine and the actor is a homomorphism only in the ultraproduct.
  kazhdan-cover-actor-models-normalize-vertex-commutants: that pulls models back from genuine finite-dimensional representations of a cover with a Kazhdan lift; this imposes nothing on the actor coordinates.
  steinberg-actor-models-carry-no-rigid-wall: that pulls models back from genuine finite-dimensional representations of the Laurent Steinberg actor; this imposes nothing on the actor coordinates.
  haagerup-targets-carry-no-relative-wall: that assumes sigma(Gamma)'' Haagerup inside M itself; here the ultraproduct of atomic coordinate images can be diffuse and non-Haagerup, and only the coordinate images are atomic.
  hs-stable-vertex-rounding-for-every-model: that is the open flexible HS-stability hypothesis (H1) for every matrix model; this verifies (H1) exactly, after a transfer, for models whose vertex coordinates are already genuine and atomic.
  kt-hyperlinear-coset-wreath-forces-nonroundable-vertex: that says a hyperlinear coset wreath forces a non-roundable vertex in matrix models; this excludes a class of II_1-coordinate candidate witnesses, with no wreath and no hyperlinearity input.
  kt-canonical-hs-normalization-fails: that is the open existence of a Connes-embeddable witness; this proves that no model with genuine atomic, equivalently amenable, vertex coordinates is one.
  theorem-e-vertex-rounds-to-unit-type-representations: that asks every tracial ultraproduct model to round on the vertex to unit-type representations; this concerns only models with genuine atomic vertex coordinates and concludes normalization, not a rounding.
artifacts:
  - research/artifacts/kt-ii1-coordinate-model-transfer-2026-09-16.md
---

Let `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)` be the explicit Theorem E pair,
with `r, d >= 3`. Let:
- `ω` be an ultrafilter on `N`, free or not;
- `(M_i, τ_i)` be Connes-embeddable finite tracial algebras, and `M = prod_ω M_i`;
- `σ : G -> U(M)` be a homomorphism, with **no condition** on `τ ∘ σ` and no injectivity.

1. **Atomic coordinates.** Suppose there are homomorphisms `ρ_i : Γ -> U(M_i)` such that

   ```text
   ρ_i(Γ)''  is atomic (a countable direct sum of matrix algebras) for every i,
   σ(γ) = [ (ρ_i(γ))_i ]_ω  for every γ in Γ.                                    (GA)
   ```

   Then `σ(G)` normalizes `σ(Γ)' ∩ M`, i.e. `<<Γ>>_G` commutes with `σ(Γ)' ∩ M`.
2. **Haagerup coordinates.** The same conclusion holds if each `ρ_i(Γ)''` has the Haagerup property
   instead. This covers every amenable `M_i`, such as `M_i = R`. It also covers every
   Connes-embeddable `M_i` with separable predual and the Haagerup property.

**Reading.**
- Since `Γ` has property (T), atomic, amenable and Haagerup are the same condition on `ρ_i(Γ)''`. (GA)
  says the vertex coordinates are genuine with amenable images. It suffices to check (GA) on a
  generating set of `Γ`, and on an `ω`-large set of indices.
- **Why it holds.** The model is transferred, not the per-model claims.
  - Connes embedding puts a separable piece of each coordinate, containing chosen commutant
    witnesses, into a matrix ultraproduct.
  - Atomic embeddings into a matrix ultraproduct are unitarily conjugate. So the conjugated vertex
    coordinates are genuine representations, with real multiplicities absorbed by integer parts.
  - Tensoring with regular representations of finite quotients of the residually finite `G` makes
    the model trace-preserving.
  - Re-indexing by dimension gives a trace-preserving model on `prod_U M_n` satisfying (H1) of
    `hs-normalization-needs-coarse-actor-scale-pinning` with zero error.
  - The commutation stabilizer only shrinks along the way. The established rounding chain then
    normalizes the transferred model, and the stabilizer inclusion carries this back.
- **What it kills.** Popa's second independence case, as recorded under
  `kt-canonical-hs-normalization-fails` with coordinates `M_n = R` and genuine vertex coordinates,
  produces no witness. The conditional recorded there, whether the chain transfers to II_1
  coordinates, is settled in the positive.
- **Sharp.** With constant coordinates `M_i = M_0`, `ρ_i = σ_0|Γ` and `σ` diagonal, removing
  atomicity turns item 1 into the negation of `kt-canonical-hs-normalization-fails`. So a witness
  with genuine vertex coordinates must have non-amenable coordinate images inside non-Haagerup
  coordinate algebras, e.g. `M_i = L(Γ) (tensor) R`.
- **Not covered.** Vertex coordinates that are only asymptotically multiplicative with atomic
  images. Their transferred matrix models need the open flexible HS-stability
  `hs-stable-vertex-rounding-for-every-model`.

No root is affected. Derivation: `kt-genuine-atomic-vertex-coordinate-models-normalize-proof`.
