import GroupApproximation.Sofic.MarkedCompressionInclusionData

/-!
# Nontrivial marked words force genuinely proper compression

The analytic marked-compression theorem only assumes the one-sided inclusion

`t * ι(Γ) * t⁻¹ ⊆ ι(Γ)`.

This file records the elementary algebraic reason that a nontrivial marked
word cannot occur when that inclusion is equality.  More precisely, if the
distinguished point `ι(a)` already lies in the conjugated image, then the
transported lamp `t c t⁻¹` commutes with `ι(a)`, so the marked commutator is
trivial.  Consequently a nontrivial marked word forces the image subgroup
`ι(Γ)` to be infinite: conjugation defines an injective self-map of that
image, and an injective self-map of a finite type is surjective.

This isolates the structural reason that the marked-compression obstruction
cannot collide with a finite image of the Kazhdan subgroup.
-/

namespace GroupApproximation

universe u

namespace MarkedCompressionInclusionData

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-- If the distinguished point belongs to the compressed image, then the
marked word is trivial. -/
theorem word_eq_one_of_exists_compressed_preimage
    (D : MarkedCompressionInclusionData Γ E)
    (ha : ∃ γ : Γ, D.iota D.a = D.t * D.iota γ * D.t⁻¹) :
    D.word = 1 := by
  obtain ⟨γ, hγ⟩ := ha
  have hcomm : Commute (D.t * D.c * D.t⁻¹) (D.iota D.a) := by
    rw [hγ]
    exact (D.comm_c γ).conj D.t
  have hconj :
      D.iota D.a * (D.t * D.c * D.t⁻¹) * (D.iota D.a)⁻¹ =
        D.t * D.c * D.t⁻¹ :=
    hcomm.symm.mul_inv_cancel
  rw [word, markedCompressionWord, hconj, commutatorElement_self]

/-- Contrapositive form: a nontrivial marked word certifies that `ι(a)` is
missing from the compressed image `t * ι(Γ) * t⁻¹`. -/
theorem iota_a_not_in_compressed_image_of_word_ne_one
    (D : MarkedCompressionInclusionData Γ E) (hne : D.word ≠ 1) :
    ¬ ∃ γ : Γ, D.iota D.a = D.t * D.iota γ * D.t⁻¹ := by
  intro ha
  exact hne (D.word_eq_one_of_exists_compressed_preimage ha)

/-- Conjugation by the compressing element, restricted to the image of the
Kazhdan subgroup.  The one-sided compression hypothesis makes this a
self-map of `ι(Γ)`. -/
noncomputable def compressedImageEndomap
    (D : MarkedCompressionInclusionData Γ E) :
    D.iota.range → D.iota.range := fun x => by
  refine ⟨D.t * (x : E) * D.t⁻¹, ?_⟩
  obtain ⟨γ, hγ⟩ := x.property
  obtain ⟨δ, hδ⟩ := D.compresses γ
  refine ⟨δ, ?_⟩
  calc
    D.iota δ = D.t * D.iota γ * D.t⁻¹ := hδ.symm
    _ = D.t * (x : E) * D.t⁻¹ := by rw [hγ]

/-- Conjugation is injective on the image subgroup. -/
theorem compressedImageEndomap_injective
    (D : MarkedCompressionInclusionData Γ E) :
    Function.Injective D.compressedImageEndomap := by
  intro x y hxy
  apply Subtype.ext
  have hxy' := congrArg Subtype.val hxy
  change D.t * (x : E) * D.t⁻¹ = D.t * (y : E) * D.t⁻¹ at hxy'
  calc
    (x : E) = D.t⁻¹ * (D.t * (x : E) * D.t⁻¹) * D.t := by group
    _ = D.t⁻¹ * (D.t * (y : E) * D.t⁻¹) * D.t := by rw [hxy']
    _ = (y : E) := by group

/-- A finite image cannot support a nontrivial marked word: on a finite
image, the injective compression endomap is surjective, so it must hit the
distinguished point. -/
theorem word_eq_one_of_finite_iota_range
    (D : MarkedCompressionInclusionData Γ E) [Finite D.iota.range] :
    D.word = 1 := by
  have hsurj : Function.Surjective D.compressedImageEndomap :=
    Finite.surjective_of_injective D.compressedImageEndomap_injective
  let xa : D.iota.range := ⟨D.iota D.a, ⟨D.a, rfl⟩⟩
  obtain ⟨x, hx⟩ := hsurj xa
  obtain ⟨γ, hγ⟩ := x.property
  apply D.word_eq_one_of_exists_compressed_preimage
  refine ⟨γ, ?_⟩
  have hx' := congrArg Subtype.val hx
  change D.t * (x : E) * D.t⁻¹ = D.iota D.a at hx'
  rw [← hγ] at hx'
  exact hx'.symm

/-- A nontrivial marked word forces the actual image subgroup `ι(Γ)` to be
infinite.  No injectivity hypothesis on `ι` is needed. -/
theorem infinite_iota_range_of_word_ne_one
    (D : MarkedCompressionInclusionData Γ E) (hne : D.word ≠ 1) :
    Infinite D.iota.range := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite D.iota.range := hfinite
  exact hne D.word_eq_one_of_finite_iota_range

end MarkedCompressionInclusionData

namespace MarkedCompressionData

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-- For endomorphism-based data, membership of `a` in the range of the
compressing endomorphism is a concrete sufficient condition for triviality
of the marked word. -/
theorem word_eq_one_of_a_mem_range_alpha
    (D : MarkedCompressionData Γ E) (ha : D.a ∈ Set.range D.alpha) :
    D.word = 1 := by
  obtain ⟨γ, hγ⟩ := ha
  have hcompressed :
      ∃ δ : Γ, D.iota D.a = D.t * D.iota δ * D.t⁻¹ := by
    refine ⟨γ, ?_⟩
    simpa only [hγ] using (D.compress γ).symm
  have h := D.toInclusionData.word_eq_one_of_exists_compressed_preimage hcompressed
  simpa using h

/-- Thus nontriviality of the marked word forces the chosen element outside
the range of the compressing endomorphism. -/
theorem a_not_mem_range_alpha_of_word_ne_one
    (D : MarkedCompressionData Γ E) (hne : D.word ≠ 1) :
    D.a ∉ Set.range D.alpha := by
  intro ha
  exact hne (D.word_eq_one_of_a_mem_range_alpha ha)

end MarkedCompressionData

end GroupApproximation
