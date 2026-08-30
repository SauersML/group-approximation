import GroupApproximation.Analysis.CalkinCStarAlgebra
import GroupApproximation.Analysis.VoiculescuAbsorption

/-!
# The Calkin-compatibility seam in Enders--Shulman Theorem 4.11

Voiculescu's Calkin uniqueness statement is deliberately phrased in
`Analysis/VoiculescuAbsorption` without naming the quotient: it returns a
unitary for which the pointwise difference is compact.  The construction in
Enders--Shulman 4.11, however, consumes an equality of bundled
`StarAlgHom`s into the Calkin algebra.  This file proves that passage.

There is no factor-map injectivity claim here.  Equality of the two
restrictions in the Calkin algebra is step 4 of the printed proof; detecting
the original amalgam through the `(1,1)` corner is the separate step 5.  In
particular, Calkin compatibility alone does not imply
`ShulmanSymmetricDouble.CompatibleTargetPairStatement`.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

variable {C H : Type} [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A representation followed by the Calkin quotient. -/
def calkinRepresentation (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    C →⋆ₐ[ℂ] CalkinAlgebra.CalkinQuotient H :=
  (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H)).comp sigma

@[simp] theorem calkinRepresentation_apply
    (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : C) :
    calkinRepresentation sigma a =
      Ideal.Quotient.mk (CalkinAlgebra.compactIdeal H) (sigma a) :=
  rfl

/-- Conjugate a representation by a unitary and then pass to the Calkin
quotient.  This is the left leg used in the Enders--Shulman compatible pair. -/
def calkinConjugateRepresentation (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (u : unitary (H →L[ℂ] H)) :
    C →⋆ₐ[ℂ] CalkinAlgebra.CalkinQuotient H :=
  (CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal H)).comp
    ((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u).toStarAlgHom.comp sigma)

@[simp] theorem calkinConjugateRepresentation_apply
    (sigma : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (u : unitary (H →L[ℂ] H)) (a : C) :
    calkinConjugateRepresentation sigma u a =
      Ideal.Quotient.mk (CalkinAlgebra.compactIdeal H)
        ((u : H →L[ℂ] H) * sigma a * star (u : H →L[ℂ] H)) := by
  rw [calkinConjugateRepresentation, StarAlgHom.comp_apply,
    StarAlgHom.comp_apply, CStarTensor.quotientStarMk_apply]
  change Ideal.Quotient.mk (CalkinAlgebra.compactIdeal H)
      ((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) (sigma a)) = _
  rw [Unitary.conjStarAlgAut_apply]

/-- Compact unitary-conjugacy is exactly equality of the two bundled Calkin
representations. -/
theorem calkinConjugateRepresentation_eq_iff
    (sigma tau : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (u : unitary (H →L[ℂ] H)) :
    calkinConjugateRepresentation sigma u = calkinRepresentation tau ↔
      ∀ a : C, IsCompactOperator
        ((u : H →L[ℂ] H) * sigma a * star (u : H →L[ℂ] H) - tau a) := by
  constructor
  · intro h a
    have ha := DFunLike.congr_fun h a
    rw [calkinConjugateRepresentation_apply, calkinRepresentation_apply,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
    exact (CalkinAlgebra.mem_compactIdeal H).mp ha
  · intro h
    apply StarAlgHom.ext
    intro a
    rw [calkinConjugateRepresentation_apply, calkinRepresentation_apply,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact (CalkinAlgebra.mem_compactIdeal H).mpr (h a)

/-- **The exact Voiculescu-to-Enders--Shulman seam.**  Assuming (V5), two
essential representations become a compatible pair after conjugating the
first leg and passing to the Calkin quotient. -/
theorem exists_calkinCompatiblePair_of_calkinUniqueness
    (hV5 : CalkinUniquenessStatement)
    [TopologicalSpace.SeparableSpace C] [TopologicalSpace.SeparableSpace H]
    (sigma tau : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hsigma : ∀ a : C, IsCompactOperator (sigma a) → a = 0)
    (htau : ∀ a : C, IsCompactOperator (tau a) → a = 0) :
    ∃ u : unitary (H →L[ℂ] H),
      calkinConjugateRepresentation sigma u = calkinRepresentation tau := by
  obtain ⟨u, hu, hcompact⟩ := hV5 C H sigma tau hsigma htau
  exact ⟨⟨u, hu⟩,
    (calkinConjugateRepresentation_eq_iff sigma tau ⟨u, hu⟩).2 hcompact⟩

end

end ShulmanFill
end GroupApproximation
