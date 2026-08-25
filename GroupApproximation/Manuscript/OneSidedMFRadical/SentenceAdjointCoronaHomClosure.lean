import GroupApproximation.Analysis.AdjointDefectEstimate

/-!
# The exact adjoint corona homomorphism

This file closes sentence-census row 137.  The coordinate conjugation maps
are first put into the manuscript's matrix-unit coordinates by
`OpAlmostRepresentation.adjoint.naturalizeCoordinates`.  Their operator-norm
multiplication defects vanish, so quotienting by the cofinite null subgroup
turns their classes into an exact group homomorphism.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- The class of the coordinate operator `Ad(V_n(g))` in the norm matrix
corona whose coordinate cardinalities are the printed squares `d_n^2`. -/
noncomputable def adjointCoronaClass (A : OpAlmostRepresentation G) (g : G) :
    NormMatrixCoronaUnitary A.adjoint.naturalizeCoordinates.model :=
  QuotientGroup.mk
    (fun n ↦ A.adjoint.naturalizeCoordinates.map n g)

/-- The multiplication defect of the naturalized adjoint coordinates lies in
the cofinite null subgroup.  This is the precise quotient step between the
asymptotic coordinate action and the exact corona action. -/
theorem adjointCoronaMultiplicationDefect_mem_null
    (A : OpAlmostRepresentation G) (g h : G) :
    (fun n ↦ A.adjoint.naturalizeCoordinates.map n g *
        A.adjoint.naturalizeCoordinates.map n h)⁻¹ *
        (fun n ↦ A.adjoint.naturalizeCoordinates.map n (g * h)) ∈
      nullCofiniteOpSubgroup A.adjoint.naturalizeCoordinates.model := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ :=
    A.adjoint.naturalizeCoordinates.asymptoticallyMultiplicative
      g h (epsilon / 2) (by linarith)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop N] with n hn
  change opLength (A.adjoint.naturalizeCoordinates.model n)
    ((A.adjoint.naturalizeCoordinates.map n g *
        A.adjoint.naturalizeCoordinates.map n h)⁻¹ *
      A.adjoint.naturalizeCoordinates.map n (g * h)) < epsilon
  rw [opLength_inv_mul]
  exact (hN n hn).trans_lt (by linarith)

/-- The printed map `g ↦ sigma-tilde(g)` as an exact homomorphism into the
norm matrix corona of the coordinate adjoint operators. -/
noncomputable def adjointCoronaHom (A : OpAlmostRepresentation G) :
    G →* NormMatrixCoronaUnitary A.adjoint.naturalizeCoordinates.model :=
  MonoidHom.mk' (adjointCoronaClass A) (fun g h ↦ by
    change (QuotientGroup.mk
        (fun n ↦ A.adjoint.naturalizeCoordinates.map n (g * h)) :
          NormMatrixCoronaUnitary A.adjoint.naturalizeCoordinates.model) =
      QuotientGroup.mk
          (fun n ↦ A.adjoint.naturalizeCoordinates.map n g) *
        QuotientGroup.mk
          (fun n ↦ A.adjoint.naturalizeCoordinates.map n h)
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq.mpr
      (adjointCoronaMultiplicationDefect_mem_null A g h)).symm)

@[simp] theorem adjointCoronaHom_apply
    (A : OpAlmostRepresentation G) (g : G) :
    adjointCoronaHom A g = adjointCoronaClass A g := rfl

/-- **Sentence-census row 137.**  The coordinate classes are not merely an
asymptotically multiplicative family: they are the values of one exact
homomorphism in the quotient.  The conclusion exposes both the representing
classes and the exact multiplication equation printed in the manuscript. -/
theorem manuscriptSentence137_exactAdjointCoronaHom
    (A : OpAlmostRepresentation G) :
    ∃ sigma : G →* NormMatrixCoronaUnitary
        A.adjoint.naturalizeCoordinates.model,
      (∀ g : G, sigma g = QuotientGroup.mk
        (fun n ↦ A.adjoint.naturalizeCoordinates.map n g)) ∧
      (∀ g h : G, sigma (g * h) = sigma g * sigma h) := by
  refine ⟨adjointCoronaHom A, ?_, ?_⟩
  · intro g
    rfl
  · intro g h
    exact map_mul (adjointCoronaHom A) g h

/-- Rows 136--137 together: matrix-unit coordinates have size `d_n^2`, and
their classes form the exact homomorphism above. -/
theorem manuscriptAdjointCoordinateSquareAndExactCoronaHom
    (A : OpAlmostRepresentation G) :
    (∀ n : ℕ,
      Fintype.card (A.adjoint.naturalizeCoordinates.model n) =
        Fintype.card (A.model n) ^ 2) ∧
      ∃ sigma : G →* NormMatrixCoronaUnitary
          A.adjoint.naturalizeCoordinates.model,
        ∀ g : G, sigma g = QuotientGroup.mk
          (fun n ↦ A.adjoint.naturalizeCoordinates.map n g) := by
  refine ⟨A.card_adjoint_naturalizeCoordinates_model, adjointCoronaHom A, ?_⟩
  intro g
  rfl

end OneSidedMFRadical
end Manuscript
end GroupApproximation
