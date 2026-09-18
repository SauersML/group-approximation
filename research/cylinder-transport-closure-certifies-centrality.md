---
rg: 2
id: cylinder-transport-closure-certifies-centrality
kind: claim
title: For any SFT extension of a rigid base over any group, base events certified at a site by locality, Boolean operations and fibre-rule steps commute with the fibre there; when every event is certified everywhere, centrality (C) holds and rigidity reduces to the pointwise fibres
requires:
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
  - quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products-proof
distinct_from:
  a2-busemann-transplants-preserve-quantum-rigidity: that proves (C) for one design by induction on sector-cylinder radius; this is the abstract closure behind that induction, for every extension over every group, with the Ã₂ Determination Lemma as one way of feeding step (T2).
  quantum-rigidity-is-not-closed-under-fibre-products: its item 3 is the special case where every certified event is a single-site event of the base.
  deterministic-extensions-of-rigid-sfts-are-rigid: that is the case of one-point fibre rules, where step (T2) alone certifies every event at every site.
---

**ESTABLISHED** (lane bh-free-09, 2026-09-18; elementary lane proof, not independently reviewed; no
priority claimed). This abstracts Step 4 of `a2-busemann-transplant-rigidity-proof` (bh-invent-04).

## Setting

The setting of `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`:
- `Y ⊆ B^Λ` and `X ⊆ (B × F)^Λ` are SFTs over a finitely generated group `Λ`, with windows `≤ D`, and
  `X` projects into `Y`;
- `Y` is `D`-quantum rigid.

Fix a `D`-family `E` of `X`.
- **Base marginals.** They form a `D`-family for `Y` (Step 2 of `deterministic-extension-rigidity-proof`),
  so they commute.
- **The map `ρ`.** By the compactness step (Step 2 of
  `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products-proof`), they define a unital
  homomorphism `ρ : LC(Y, k) → End(W_0)` sending each cylinder to the product of its base marginals.
- **Fibre rules.** For each site `v` there is a finite partition of `Y` into *germs* `[g]_v`, each
  determined by `y|_(vB_D)`. For each germ there is a finite set `F_g ⊆ B_D \ {e}` such that, for
  `(y, f) ∈ X` with `y ∈ [g]_v`, the letter `f(v)` is a function of `f|_(vF_g)` and `y|_(vB_D)`.

## Theorem

Let `𝒯` be the least set of pairs `(U, v)` (`U ⊆ Y` clopen, `v ∈ Λ`) such that:
- **(T0) Locality.** `(U, v) ∈ 𝒯` whenever `U` is determined by `y|_(vB_(2D))`.
- **(T1) Boolean.** For each `v`, `{U : (U, v) ∈ 𝒯}` is closed under complements and finite unions and
  intersections.
- **(T2) Fibre-rule step.** If `U ⊆ [g]_v` and `(U, vf) ∈ 𝒯` for every `f ∈ F_g`, then `(U, v) ∈ 𝒯`.

Then, for every `(U, v) ∈ 𝒯`, `ρ(1_U)` commutes with every fibre marginal `E^F_c(v)`, and hence with
every `E_(b,c)(v)`. If `𝒯` contains every pair `(U, v)`, then (C) holds, and by the decomposition
theorem `X` is `D`-rigid if and only if it is `D`-rigid relative to every base point.

**Proof.** Induct along the construction of `𝒯`, for all `D`-families at once.
- **(T0).** `ρ(1_U)` is a polynomial in base marginals at sites within `2D` of `v`, so (Q2) applies.
- **(T1).** The elements of `ρ(LC(Y, k))` commuting with a fixed operator form a subalgebra of a
  commutative algebra of idempotents. The idempotents `1 − e`, `ee'` and `e + e' − ee'` stay in it.
- **(T2).**
  - *The rule as an operator identity.* A ball sum on `vB_D` (Lemma 1 of
    `determinism-closure-certifies-quantum-rigidity`; Step 3 of `a2-busemann-transplant-rigidity-proof`)
    gives `P E^F_c(v) = P Φ` with `P = ρ(1_([g]_v))`. Here `Φ` is a polynomial in the fibre marginals
    at `vF_g` and the base marginals on `vB_D`. All these sites lie in `vB_D`, so the factors of `Φ`,
    `P` and `E^F_c(v)` commute pairwise by (Q2).
  - *`ρ(1_U)` commutes with `Φ`.* By induction, `ρ(1_U)` commutes with each fibre marginal at `vf`.
    It commutes with base marginals because the base is rigid.
  - *The computation.* Since `ρ(1_U) = ρ(1_U) P`,

    ```text
    ρ(1_U) E^F_c(v) = ρ(1_U) P Φ = ρ(1_U) Φ,
    E^F_c(v) ρ(1_U) = E^F_c(v) P ρ(1_U) = P Φ ρ(1_U) = ρ(1_U) P Φ = ρ(1_U) Φ.
    ```
- **Last clause.** Base marginals are `ρ` of site cylinders, which gives (C). Then apply item 3 of
  `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`. `∎`

## Instances

- **Deterministic extensions.** The rule is `F = {s^(-1)}` for `s ∈ S'`. Starting from (T0) at `u`,
  (T2) moves every event to `us`, and so to every site, since `S'` generates `Λ` as a monoid.
  This recovers Step 5 of `deterministic-extension-rigidity-proof`.
- **Fibre products.** For single-site events `U = [b at vk]`, (T0)–(T2), together with the base's own
  determinism identities, give the closure `K` of `quantum-rigidity-is-not-closed-under-fibre-products`,
  item 3.
- **`Ã₂` and tree transplants (bh-invent-04).**
  - The sector cylinder `U_S(v)` of radius `R` equals `[g]_v ∩ X_(S,u)`, where `X_(S,u)` is a union of
    radius-`(R−1)` cylinders at the expansion site `p_u`. This is the Determination Lemma.
  - By induction on `R`, `(X_(S,u), p_u) ∈ 𝒯`. Since `[g]_v` is local at `p_u`, (T0) and (T1) give
    `(U_S(v), p_u) ∈ 𝒯`, and (T2) gives `(U_S(v), v) ∈ 𝒯`.
  - (F2) says that sector cylinders at `v` generate all clopens, and (T1) then certifies everything.

## What the closure needs

**(T2) moves events only along the fibre's rules.** So an event at `v` is certified exactly when it can
be *read inside the region that the fibre's rules reach from `v`*, up to Boolean operations and locality.
- *Transplants:* (F2) says precisely this. The base is readable in the fibre's cone.
- *Fibre products:* when the base has freedom that the fibre's rules never reach,
  `cross-layer-separable-modifications-kill-quantum-rigidity` shows that failure of the closure is
  genuine, and not a limitation of the method.

## Lesson for general BH

- **(C) is proved by transport.** Base events travel along fibre rules. Every known proof of (C)
  (deterministic extensions, product groups, `Ã₂` and tree transplants) is an instance of (T0)–(T2).
- **The design target for G2** is therefore concrete: **the base configuration must be readable from
  the fibre's rule region at every site.**
- **Freedom the rules cannot see is fatal.** When the base has freedom that no fibre rule sees, and
  that freedom can be separated from the fibre's own, rigidity fails.
- **The exception is atoms.** Where a layer is a single classical point on one side of an interface
  (the relative-seed atoms), transport is not needed at all.
