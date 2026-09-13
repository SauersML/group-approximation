---
rg: 2
id: o2-contractible-crossed-product-inner-half-flip-mcduff-proof
kind: route
title: The unit class of the crossed product kills both factor embeddings, Gabe--Szabó uniqueness gives the half-flip, a slice-map telescope kills the tensor power, and Szabó's McDuff theorem closes the loop
target: o2-contractible-crossed-product-inner-half-flip-mcduff
requires:
  - gabe-szabo-unital-uniqueness-theorem
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
---

**Sources.**
* Gabe--Szabó Theorem 5.8 and Proposition 3.15, as imported in
  `gabe-szabo-unital-uniqueness-theorem`.
* Szabó, arXiv:1509.08380 (read 2026-09-13):
  - the definition before Proposition 3.3: `(D, γ)` has approximately G-inner
    half-flip "if the two equivariant \*-homomorphisms `id_D ⊗ 1, 1 ⊗ id_D`"
    into `(D ⊗ D, γ ⊗ γ)` are approximately G-unitarily equivalent;
  - Proposition 3.3(ii): "The infinite tensor power (⊗_N D, ⊗_N γ) is
    strongly self-absorbing", with the reindexation remark in its proof;
  - Definition 3.1 and Theorem 3.7, (ii) ⟺ (iii), quoted in
    `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences-proof`.
* Meyer--Nest, arXiv:math/0312292, Definition 2.5, Proposition 2.6 and
  Lemma 2.7, as quoted in
  `o2-zp-crossed-products-absorb-uhf-p-without-uct-proof`.  Lemma 2.7 allows
  equivariant completely positive contractions.

**Standard inputs, not re-read.**
* (GJ) Green--Julg: `KK^G(C, D) ≅ K_0(D ⋊ G)`.
* (OUT) If `α_g` is outer on the simple unital `O_2`, then so are
  `α_g ⊗ α_g` and `⊗_n α_g`.
* (CC) Cocycle conjugate actions are KK^G-equivalent.
* `O_2^(⊗∞) ≅ O_2`.

**Item 1.**
* `j = id_D ⊗ ι_D`, where `ι_D : C → D` is the unital inclusion.  So
  `KK^G(j) = id_D ⊗ [ι_D]`, and `[ι_D] ∈ KK^G(C, D) ≅ K_0(O_2 ⋊_α G) = 0` by
  (GJ) and the hypothesis.  Likewise `KK^G(k) = [ι_D] ⊗ id_D = 0`.
* Theorem 5.8 applies with `A = O_2`, which is exact, and `B = O_2 ⊗ O_2`, a
  unital Kirchberg algebra.  The action `β = α ⊗ α` is amenable (`G` is
  finite) and pointwise outer by (OUT), hence isometrically shift-absorbing by
  Proposition 3.15.  `j` and `k` are unital embeddings with equal classes.
* So there is a continuous unitary path `v_t` with `Ad(v_t) ∘ j → k` and
  `‖1 − v_t β_g(v_t)*‖ → 0`.  Sampling gives the approximate G-unitary
  equivalence in Szabó's definition.

**Item 2.**
* *Strong self-absorption.*  Proposition 3.3(ii) with `(D, γ) = (O_2, α)`.
* *Contractibility.*  Put `A_m = O_2^(⊗m)` with connecting maps `x ↦ x ⊗ 1`.
  Let `ω` be an `α`-invariant state (average any state over `G`), and
  `φ_m = id ⊗ ω^(⊗∞) : O_2^(⊗∞) → O_2^(⊗m)`.  These are equivariant completely
  positive contractions.  `(α_m^∞ ∘ φ_m)(x) = x` once `x` lies in the first `m`
  factors, so by contractivity `α_m^∞ ∘ φ_m → id` pointwise.  By Lemma 2.7 the
  system is admissible.  Proposition 2.6 gives the Milnor sequence
  `0 → lim^1 KK^G_(*+1)(A_m, Y) → KK^G_*(A_∞, Y) → lim KK^G_*(A_m, Y) → 0`.
  Each connecting map is `id_(D^(⊗m)) ⊗ [ι_D] = 0`, so `lim` and `lim^1`
  vanish, and `KK^G(A_∞, Y) = 0` for all `Y`.
* *Rokhlin.*  `α^(⊗∞)` is pointwise outer by (OUT) and contractible, so item 2
  of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` makes it conjugate to
  `id ⊗ μ_G`, with the Rokhlin property.

**Item 3.**
* *Rokhlin ⟹ McDuff.*  Item 2 of the Rokhlin characterization makes `α`
  conjugate to `γ = id ⊗ μ_G` on `O_2 ⊗ M_(|G|^∞)`.  This `γ` is strongly
  self-absorbing, by Proposition 3.3(ii) applied to
  `(O_2 ⊗ M_(|G|), id ⊗ Ad λ)`.  That system has approximately G-inner
  half-flip: the flip unitary of `ℓ²G ⊗ ℓ²G` is fixed by `Ad(λ ⊗ λ)`, and the
  half-flip of `O_2` is approximately inner, with the trivial action.  Its
  infinite tensor power is `γ`.  Definition 3.1 gives `γ ≅ γ ⊗ γ`, and
  Theorem 3.7, (ii) ⟹ (iii), with `α = γ` gives a unital equivariant map from
  `γ` into its central sequences.  Transport along the conjugacy.
* *McDuff ⟹ absorption.*  The standard reindexation, stated in the proof of
  Proposition 3.3(ii), upgrades a unital equivariant `(O_2, α) → F_∞(O_2)` to
  one from `(O_2^(⊗∞), α^(⊗∞))`.  Since `α^(⊗∞)` is strongly self-absorbing by
  item 2, Theorem 3.7, (iii) ⟹ (ii), gives `α ≃_cc α ⊗ α^(⊗∞)`.
* *Absorption ⟹ Rokhlin.*  By (CC) and item 2,
  `D ≃ D ⊗ (O_2^(⊗∞), α^(⊗∞)) ≃ D ⊗ 0 = 0`.  Item 2 of the Rokhlin
  characterization then gives the Rokhlin property.
