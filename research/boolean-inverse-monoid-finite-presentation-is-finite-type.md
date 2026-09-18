---
rg: 2
id: boolean-inverse-monoid-finite-presentation-is-finite-type
kind: claim
title: The Boolean inverse monoid of a subshift crossed product, with or without Thompson's V, is finitely presented exactly when the subshift is of finite type
distinct_from:
  sft-crossed-product-fp-iff-quantum-rigid: that characterizes finite presentation of the crossed-product ALGEBRA, where commutation of translated idempotents must be forced and quantum rigidity appears; this is the Boolean inverse monoid, where idempotents commute by axiom, and only finite type remains.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that is about the group of units F(T); this is about the Boolean inverse monoid B(T) whose group of units is F(T). Together they show the units functor does not preserve finite presentation (fp-boolean-inverse-monoids-need-not-have-fp-full-groups).
artifacts:
  - research/artifacts/gq-bh-bh-invent-03-groupoid-higman.md
---

**ESTABLISHED (lane proof, bh-invent-03, unreviewed; no priority claimed).** Route:
`boolean-inverse-monoid-finite-presentation-is-finite-type-proof`.

**Setting.**
- `Λ = ⟨S | R⟩` is a group with finite symmetric generating set `S`. `X ⊆ A^Λ` is a subshift over
  a finite alphabet, with `(λ.x)(h) = x(λ^(-1) h)`. No freeness or minimality is assumed.
- `𝒦 = Λ ⋉ X` is the transformation groupoid. `G_V` is the groupoid of germs of Thompson's `V` on
  `C = {0,1}^N` (the Cuntz groupoid), and `T = G_V × 𝒦` on `C × X`.
- `B(𝒢)` is the Boolean inverse monoid of compact open bisections of an ample Hausdorff groupoid
  `𝒢`. Its group of units is the topological full group `F(𝒢)`.
- *Presentations.* A Boolean inverse monoid `B` with a map `ι : Σ -> B` is presented by `(Σ, R)` if
  `ι(Σ)` generates `B` (under product, inverse, 0, 1 and orthogonal joins), `ι` satisfies `R`, and
  every map of `Σ` into a Boolean inverse monoid `N` satisfying `R` extends to an additive
  homomorphism `B -> N`. Here additive means it preserves 0, 1, products, inverses and orthogonal joins.
  Uniqueness is automatic.

**Theorem.**
1. **Finite type ⇒ finite presentation.** Suppose `Λ` is finitely presented and `X` is of finite type,
   with forbidden patterns `𝔽` on a finite window `W`. Then `B(𝒦)` is presented by the generators
   `u_s` (`s ∈ S`) and `e_a` (`a ∈ A`), subject to the finitely many relations below.
   - (U) Each `u_s` is a unit, and `r(u) = 1` for every relator `r ∈ R`.
   - (P) Each `e_a` is an idempotent, `e_a e_b = 0` for `a ≠ b`, and `⊕_a e_a = 1`.
   - (F) For each `α ∈ 𝔽`, `∏_(w ∈ W) u_w e_(α(w)) u_w^(-1) = 0`, with `u_w` a fixed word for `w`.

   Adding `y_0, y_1` with (C) `y_i^(-1) y_i = 1` and `y_0 y_0^(-1) ⊕ y_1 y_1^(-1) = 1`, and (M) each `y_i`
   commuting with every `u_s` and every `e_a`, presents `B(T)`.
2. **Finite presentation ⇒ finite type.** Suppose `Λ` is finitely generated and `B(𝒦)`, or `B(T)`, is
   finitely presented. Then `X` is of finite type.

So in the category of Boolean inverse monoids, finite presentation of the crossed product (with or
without `V`) is exactly finite type. **No rigidity hypothesis appears.** The relation that the translated
idempotents `u_λ e_a u_λ^(-1)` all commute costs nothing, because a Boolean inverse monoid's idempotents
commute by axiom.

**Why it matters (lesson for general BH).**
- For groupoids, the natural algebraic notion of "finitely presented" is a finite presentation of
  `B(𝒢)`. The theorem says this notion is *cheap*: every SFT crossed product has it, rigid or not.
- The full group, which is what Boone–Higman needs, is the group of units `U(B(𝒢))`.
  `fp-v-times-subshift-full-groups-force-quantum-rigidity` shows `U` can fail to preserve finite
  presentation, and `fp-boolean-inverse-monoids-need-not-have-fp-full-groups` gives explicit cases.
- The whole gap between "finite type" and "finitely presented full group" is therefore the passage from
  a Boolean inverse monoid to its group of units. That passage loses exactly the axiom "idempotents
  commute". This is where quantum rigidity (master route gate G2) lives. The open conjecture
  `rigid-boolean-inverse-monoid-presentations-have-fp-full-groups` states the resulting notion for all
  ample groupoids.
- A Higman-type embedding theorem in the plain Boolean-inverse-monoid category reduces to existence of
  free SFTs over finitely presented overgroups, gate P1
  (`decidable-groups-embed-in-fp-groups-with-minimal-free-sft`). The rigidity gate is invisible there,
  so it must be imposed on the presentation.

**Inputs.**
- Stone duality for Boolean algebras.
- The fact that the orthogonal-join Boolean inverse monoids form a variety, which gives Tietze
  transformations. This is recalled from Wehrung, *Refinement monoids, equidecomposability types and
  Boolean inverse semigroups*, LNM 2188 (2017), and was not re-read. It is used only in part 2 to change
  generating sets. Part 1 does not use it.
