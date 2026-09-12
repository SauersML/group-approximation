import GroupApproximation.Kazhdan.GHBHyperbolicFilling
import GroupApproximation.GGT.SystolicDiscCounts
import GroupApproximation.Meta.AxiomGuard

/-!
# The typed count and boundary sums at the coset complex of `GHB(7)`

`GHBHyperbolicFilling.lean` derives `IsHyperbolicGroup (GHB 7)` over four inputs: the zip and
fold moves of triangulated discs in the coset complex, the typed count `TypedCountStatement`
(HC11) and the boundary sums `BoundarySumStatement` (HC12).  This module discharges the last
two, from `Systolic.TriangulatedDisc.exists_typedCounts` with
`TypedTriangularDiscCounts.faceCount_le_six_mul_boundaryLength`, and from
`Systolic.TriangulatedDisc.abs_boundarySum_le`:

* `typedCountStatement_of_typed`: in a complex whose triangles have three distinct types
  `τ : V → Fin 3`, a disc meeting the typed girth `6, 8, 8` at its interior vertices has at
  most `6` triangles per boundary edge;
* `boundarySumStatement`: HC12 holds in every triangle complex;
* `CCKW.typedCountStatement_cosetComplex`: the coset complex, typed by `Sigma.fst`;
* `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold`: `IsHyperbolicGroup (GHB 7)` over the zip
  and fold moves alone.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route (hyperbolicity of `GHB(7)`); certifies no manuscript step on its
own.
-/

namespace GroupApproximation
namespace GHBHyperbolicStokes

open Systolic

universe u

variable {V : Type u}

/-- **HC11.**  In a complex whose triangles have three distinct types, a disc meeting the typed
girth at its interior vertices has at most `6` triangles per boundary edge. -/
theorem typedCountStatement_of_typed {X : TriangleComplex V} (τ : V → Fin 3)
    (hτ : ∀ x y z, X.Tri x y z → τ x ≠ τ y ∧ τ y ≠ τ z ∧ τ x ≠ τ z) :
    TypedCountStatement X (typedGirth τ) := by
  intro γ D hdeg
  obtain ⟨C, hF, hB⟩ := D.exists_typedCounts τ (fun h => hτ _ _ _ h) hdeg
  have h := C.faceCount_le_six_mul_boundaryLength
  omega

/-- **HC12.**  Boundary sums are bounded by triangle sums in every triangle complex. -/
theorem boundarySumStatement (X : TriangleComplex V) : BoundarySumStatement X := by
  intro γ D I hanti C₀ htri
  exact D.abs_boundarySum_le I hanti (fun h => htri _ _ _ h)

end GHBHyperbolicStokes

namespace KMSGroup
namespace CCKW

open GHBHyperbolicStokes

/-- The triangles of the coset complex have three distinct types. -/
theorem type_ne_of_cosetComplex_tri (x y z : Vertex) (h : cosetComplex.Tri x y z) :
    x.1 ≠ y.1 ∧ y.1 ≠ z.1 ∧ x.1 ≠ z.1 := by
  obtain ⟨h1, h2, h3, -⟩ := h
  exact ⟨h1, h2, h3⟩

/-- **HC11 at the coset complex of `GHB(7)`**, at the typed girth `6, 8, 8`. -/
theorem typedCountStatement_cosetComplex :
    TypedCountStatement cosetComplex (fun x : Vertex => if x.1 = 0 then 6 else 8) :=
  typedCountStatement_of_typed (fun x : Vertex => x.1) type_ne_of_cosetComplex_tri

end CCKW

namespace GHBQuotient

/-- **`GHB(7)` is hyperbolic**, over the zip and fold moves of triangulated discs in its coset
complex. -/
theorem isHyperbolicGroup_ghb7_of_zipFold (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex) :
    Hyperbolic.IsHyperbolicGroup (GHB 7) :=
  isHyperbolicGroup_ghb7_of_discInputs hzip hfold CCKW.typedCountStatement_cosetComplex
    (GHBHyperbolicStokes.boundarySumStatement _)

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.GHBHyperbolicStokes.typedCountStatement_of_typed
#audit_axioms GroupApproximation.GHBHyperbolicStokes.boundarySumStatement
#audit_axioms GroupApproximation.KMSGroup.CCKW.typedCountStatement_cosetComplex
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold
