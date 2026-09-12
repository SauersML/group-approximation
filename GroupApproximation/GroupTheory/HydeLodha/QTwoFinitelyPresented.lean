import GroupApproximation.GroupTheory.HydeLodha.QTwoBrown
import GroupApproximation.GroupTheory.HydeLodha.QTwoBrownTriangle
import GroupApproximation.GroupTheory.HydeLodha.QTwoStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# `Q₂` is finitely presented

Hyde–Lodha, Theorem 4.8: "Each `Γ` satisfying `Q_n ≤ Γ ≤ Γ_n` is of type `F_∞`", at `n = 2`, in the
finite-presentation form the manuscript's Fournier-Facio paragraph needs.

The two inputs of `QTwoBrown.isFinitelyPresented_of_stabK_triangle` are Proposition 4.7 (`stabK Γ K`
finitely presented) and the triangle count of double cosets of the vertex stabilizer.  The triangle count
is `vertexH_triangle` (`QTwoBrownTriangle`) and is discharged here (`vertexHTriangle`), so the `_of_stabK`
endpoints take Proposition 4.7 as their only hypothesis.  Once Proposition 4.7 lands, the closed endpoints
`isFinitelyPresented_qTwo` and `finitelyPresentedInfiniteSimpleStatement` will be added here.
-/

namespace GroupApproximation
namespace HydeLodha

open DoubleCosetPresentation Manuscript.NonMF.TorsionFreePrinted

/-- Proposition 4.7, finite-presentation form, as a named hypothesis. -/
def StabKFinitelyPresented (Γ : Subgroup (Equiv.Perm ℚ)) : Prop :=
  ∀ K : Set ℚ, K.Finite → K.Nonempty → (∀ k ∈ K, Dyadic6 k) → Group.IsFinitelyPresented ↥(stabK Γ K)

/-- The triangle count of Brown's criterion at the vertex `0 + ℤ`, as a named hypothesis. -/
def VertexHTriangle (Γ : Subgroup (Equiv.Perm ℚ)) : Prop :=
  ∀ t' t : ↥Γ, ∃ A : Finset ↥(vertexH Γ), ∀ a : ↥(vertexH Γ),
    ∃ c : ↥(edgeStab (vertexH Γ) t'⁻¹), ∃ d : ↥(edgeStab (vertexH Γ) t),
    ∃ a₀ ∈ A, a = (c : ↥(vertexH Γ)) * a₀ * d

/-- **Hyde–Lodha, Theorem 4.8 (finite presentation)**, over Proposition 4.7 and the triangle count. -/
theorem isFinitelyPresented_of_qTwo_le_of_inputs {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ)
    (hΓ : Γ ≤ gammaTwo) (h47 : StabKFinitelyPresented Γ) (htri : VertexHTriangle Γ) :
    Group.IsFinitelyPresented ↥Γ :=
  isFinitelyPresented_of_stabK_triangle hQ hΓ h47 htri

/-- `Q₂` is finitely presented, over Proposition 4.7 and the triangle count. -/
theorem isFinitelyPresented_qTwo_of_inputs (h47 : StabKFinitelyPresented qTwo)
    (htri : VertexHTriangle qTwo) : Group.IsFinitelyPresented ↥qTwo :=
  isFinitelyPresented_of_qTwo_le_of_inputs le_rfl qTwo_le_gammaTwo h47 htri

/-- A finitely presented torsion-free infinite simple group, over Proposition 4.7 and the triangle
count. -/
theorem finitelyPresentedInfiniteSimpleStatement_of_inputs (h47 : StabKFinitelyPresented qTwo)
    (htri : VertexHTriangle qTwo) : FinitelyPresentedInfiniteSimpleStatement :=
  finitelyPresentedInfiniteSimpleStatement_of_isFinitelyPresented_qTwo
    (isFinitelyPresented_qTwo_of_inputs h47 htri)

/-- The triangle count holds for every `Q₂ ≤ Γ ≤ Γ₂` (`vertexH_triangle`). -/
theorem vertexHTriangle {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) :
    VertexHTriangle Γ :=
  vertexH_triangle hQ hΓ

/-- **Hyde–Lodha, Theorem 4.8 (finite presentation)**, over Proposition 4.7 only. -/
theorem isFinitelyPresented_of_qTwo_le_of_stabK {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ)
    (hΓ : Γ ≤ gammaTwo) (h47 : StabKFinitelyPresented Γ) : Group.IsFinitelyPresented ↥Γ :=
  isFinitelyPresented_of_qTwo_le_of_inputs hQ hΓ h47 (vertexHTriangle hQ hΓ)

/-- `Q₂` is finitely presented, over Proposition 4.7 only. -/
theorem isFinitelyPresented_qTwo_of_stabK (h47 : StabKFinitelyPresented qTwo) :
    Group.IsFinitelyPresented ↥qTwo :=
  isFinitelyPresented_of_qTwo_le_of_stabK le_rfl qTwo_le_gammaTwo h47

/-- A finitely presented torsion-free infinite simple group, over Proposition 4.7 only. -/
theorem finitelyPresentedInfiniteSimpleStatement_of_stabK (h47 : StabKFinitelyPresented qTwo) :
    FinitelyPresentedInfiniteSimpleStatement :=
  finitelyPresentedInfiniteSimpleStatement_of_inputs h47 (vertexHTriangle le_rfl qTwo_le_gammaTwo)

#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_of_qTwo_le_of_inputs
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_inputs
#audit_axioms GroupApproximation.HydeLodha.vertexHTriangle
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_of_qTwo_le_of_stabK
#audit_axioms GroupApproximation.HydeLodha.finitelyPresentedInfiniteSimpleStatement_of_stabK

end HydeLodha
end GroupApproximation
