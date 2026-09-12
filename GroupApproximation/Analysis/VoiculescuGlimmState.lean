import GroupApproximation.Analysis.VoiculescuGlimmTransport
import GroupApproximation.Analysis.StateExtension

/-!
# (V2) The state assembly: from a functional on `A` to one killing the compacts

This finishes the first of Glimm's four pieces.  Given a positive functional on
a closed `⋆`-subalgebra `A ⊆ B(H)` meeting the compacts only in `0`, it produces
a positive functional on all of `B(H)` that agrees with it on `A` and
annihilates `K(H)` — which is the object the rest of Glimm's lemma is about.

## The route, and why it goes through the quotient

A direct extension of `φ` to `B(H)` exists — that is `StateExtension` — but
there is no reason for it to kill the compacts, and correcting it afterwards
does not work: an approximate-unit average of the extension kills `K(H)` but no
longer restricts to `φ`.  The information that makes the two compatible is
`A ∩ K(H) = 0`, and the only place it can be spent is the quotient, where it
says the essential map is injective on `A`.

So: transport `φ` to the image of `A` in `Q(H)` (well defined by injectivity),
extend it there, and pull back along the quotient map.  The pullback kills
`K(H)` for free, because the quotient map does.

`Analysis/VoiculescuGlimmTransport` supplied the one step with content, that
positivity reflects along the essential map; everything here is composition.
The only piece needing an argument is that the quotient map carries positive
elements to positive elements, which is the square root: `T = √T · √T` with
`√T` self-adjoint, so `π T = (π √T)⋆ (π √T)`.

The instance ladder is copied rather than inherited — it is `local`, and every
module on this surface carries its own.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

noncomputable local instance :
    ContinuousFunctionalCalculus ℂ (CalkinAlgebra.CalkinQuotient H)
      IsStarNormal := by
  exact IsStarNormal.instContinuousFunctionalCalculus (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    NonUnitalContinuousFunctionalCalculus ℂ (CalkinAlgebra.CalkinQuotient H)
      IsStarNormal := by
  exact ContinuousFunctionalCalculus.toNonUnital (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    NonUnitalContinuousFunctionalCalculus ℝ (CalkinAlgebra.CalkinQuotient H)
      IsSelfAdjoint := by
  exact IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    (A := CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    PartialOrder (CalkinAlgebra.CalkinQuotient H) :=
  CStarAlgebra.spectralOrder (CalkinAlgebra.CalkinQuotient H)

noncomputable local instance :
    StarOrderedRing (CalkinAlgebra.CalkinQuotient H) :=
  CStarAlgebra.spectralOrderedRing (CalkinAlgebra.CalkinQuotient H)

/-- **The quotient map is positive.**  Through the square root, not through any
order-theoretic property of the quotient: `T = √T · √T` with `√T` self-adjoint,
and a `⋆`-homomorphism carries that to `(π √T)⋆ (π √T)`. -/
theorem nonneg_essential_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    0 ≤ CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) T := by
  have hsqrt : CFC.sqrt T * CFC.sqrt T = T := by
    have h := CFC.sq_sqrt T hT
    rwa [pow_two] at h
  have hsa : IsSelfAdjoint (CFC.sqrt T) := (CFC.sqrt_nonneg T).isSelfAdjoint
  have hstar : star (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H)
      (CFC.sqrt T))
      = CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) (CFC.sqrt T) := by
    rw [← map_star, hsa.star_eq]
  rw [← hsqrt, map_mul]
  have h := star_mul_self_nonneg
    (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) (CFC.sqrt T))
  rwa [hstar] at h

/-- **The extension, on the Calkin side.**  The functional transported to the
image of `A` and extended over the whole quotient.

Split off from the assembly below because the two halves together exceed the
whole-declaration elaboration budget: this half alone builds the equivalence
onto the range, a bundled linear map, the positivity transport and the
extension theorem.  Its conclusion is phrased in `essentialRestrict`, which is
the vocabulary the pullback needs, so the seam costs the consumer nothing. -/
theorem exists_quotient_extension_of_compactMem_eq_zero
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) (φ : ↥A →ₗ[ℂ] ℂ)
    (hφ : ∀ b : ↥A, 0 ≤ (b : H →L[ℂ] H) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r) :
    ∃ Ψ : CalkinAlgebra.CalkinQuotient H →ₗ[ℂ] ℂ,
      (∀ b : ↥A, Ψ (essentialRestrict A b) = φ b) ∧
      (∀ x : CalkinAlgebra.CalkinQuotient H, 0 ≤ x → ∃ r : ℝ, 0 ≤ r ∧ Ψ x = r) := by
  classical
  have hinj := injective_essentialRestrict hAK
  set e := StarAlgEquiv.ofInjective (essentialRestrict A) hinj with he
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥((essentialRestrict A).range) →ₗ[ℂ] ℂ,
      ∀ b, ψ b = φ (e.symm b) :=
    ⟨{ toFun := fun b ↦ φ (e.symm b)
       map_add' := fun x y ↦ by rw [map_add, map_add]
       map_smul' := fun c x ↦ by rw [map_smul, map_smul]; rfl }, fun _ ↦ rfl⟩
  have hψpos : ∀ b : ↥((essentialRestrict A).range),
      0 ≤ (b : CalkinAlgebra.CalkinQuotient H) → ∃ r : ℝ, 0 ≤ r ∧ ψ b = r := by
    intro b hb
    have hcoe : essentialRestrict A (e.symm b) = (b : CalkinAlgebra.CalkinQuotient H) :=
      congrArg (fun z : ↥((essentialRestrict A).range) ↦
        (z : CalkinAlgebra.CalkinQuotient H)) (e.apply_symm_apply b)
    have hpos : 0 ≤ essentialRestrict A (e.symm b) := by
      rw [hcoe]
      exact hb
    obtain ⟨r, hr0, hr⟩ := hφ (e.symm b) (nonneg_of_essential_nonneg hA hAK hpos)
    exact ⟨r, hr0, by rw [hψ b, hr]⟩
  obtain ⟨Ψ, hΨrange, hΨpos⟩ := StateExtension.exists_positive_extension hψpos
  refine ⟨Ψ, fun b ↦ ?_, hΨpos⟩
  have h1 : Ψ ((e b : ↥((essentialRestrict A).range)) : CalkinAlgebra.CalkinQuotient H)
      = ψ (e b) := hΨrange (e b)
  have h2 : ((e b : ↥((essentialRestrict A).range)) : CalkinAlgebra.CalkinQuotient H)
      = essentialRestrict A b := rfl
  rw [h2] at h1
  rw [h1, hψ, e.symm_apply_apply]

/-- **The state assembly.**  A positive functional on `A` extends to one on
`B(H)` that annihilates the compacts.

The positivity hypothesis and conclusion are in the shape `StateExtension`
uses — nonnegativity as a real value — rather than as a bundled positive linear
map, so that no repackaging happens between the two theorems. -/
theorem exists_extension_annihilating_compacts
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) (φ : ↥A →ₗ[ℂ] ℂ)
    (hφ : ∀ b : ↥A, 0 ≤ (b : H →L[ℂ] H) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r) :
    ∃ ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ,
      (∀ b : ↥A, ρ (b : H →L[ℂ] H) = φ b) ∧
      (∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0) ∧
      (∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r) := by
  obtain ⟨Ψ, hΨA, hΨpos⟩ :=
    exists_quotient_extension_of_compactMem_eq_zero hA hAK φ hφ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ,
      ∀ T, ρ T = Ψ (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) T) :=
    ⟨{ toFun := fun T ↦ Ψ (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) T)
       map_add' := fun x y ↦ by rw [map_add, map_add]
       map_smul' := fun c x ↦ by rw [map_smul, map_smul]; rfl }, fun _ ↦ rfl⟩
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro b
    rw [hρ, ← essentialRestrict_apply]
    exact hΨA b
  · intro T hT
    have h0 : CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H) T = 0 := by
      rw [CStarTensor.quotientStarMk_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((CalkinAlgebra.mem_compactIdeal H).mpr hT)
    rw [hρ, h0, map_zero]
  · intro T hT
    obtain ⟨r, hr0, hr⟩ := hΨpos _ (nonneg_essential_of_nonneg hT)
    exact ⟨r, hr0, by rw [hρ, hr]⟩

end

end ShulmanFill
end GroupApproximation
