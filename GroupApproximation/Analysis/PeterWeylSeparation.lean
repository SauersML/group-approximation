import GroupApproximation.Analysis.PeterWeylProfinite
import GroupApproximation.External.TauCeti.RepresentationTheory.Compact.RepresentativeDensity
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite-dimensional representations separate compact groups

The vendored Tau Ceti development proves the Peter--Weyl density theorem and
extracts a finite-dimensional continuous representation separating any two
points of a compact Hausdorff group.  This file translates that representation
to the matrix-valued formulation used by `PeterWeyl.SeparatesPoints`.
-/

namespace GroupApproximation
namespace PeterWeyl

noncomputable section

universe u

/-- Matrix coordinates of a continuous representation on a finite-dimensional
complex inner-product space. -/
def contRepresentationMatrixHom
    {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (pi : ContRepresentation ℂ G V) :
    G →* Matrix (Fin (Module.finrank ℂ V))
      (Fin (Module.finrank ℂ V)) ℂ := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V :=
    (stdOrthonormalBasis ℂ V).toBasis
  exact
    { toFun := fun g => LinearMap.toMatrix b b (pi g).toLinearMap
      map_one' := by
        rw [map_one]
        exact LinearMap.toMatrix_id b
      map_mul' := by
        intro g h
        rw [map_mul]
        exact LinearMap.toMatrix_comp b b b _ _ }

/-- Equality of the coordinate matrices reflects equality of the action
operators. -/
theorem contRepresentationMatrixHom_injective_on_operators
    {G V : Type*} [Group G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (pi : ContRepresentation ℂ G V) {g h : G}
    (heq : contRepresentationMatrixHom pi g =
      contRepresentationMatrixHom pi h) :
    pi g = pi h := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V :=
    (stdOrthonormalBasis ℂ V).toBasis
  have hlin : (pi g).toLinearMap = (pi h).toLinearMap := by
    change LinearMap.toMatrix b b (pi g).toLinearMap =
      LinearMap.toMatrix b b (pi h).toLinearMap at heq
    have h := congrArg (Matrix.toLin b b) heq
    simpa using h
  ext v
  exact LinearMap.congr_fun hlin v

/-- Peter--Weyl point separation in the matrix form used by the Bohr-radical
calculus. -/
theorem separatesPoints : SeparatesPoints.{u} := by
  intro C c hc
  obtain ⟨n, pi, _hcontinuous, hpi⟩ :=
    TauCeti.exists_contRepresentation_apply_ne (𝕜 := ℂ) c 1 hc
  let rho := contRepresentationMatrixHom pi
  refine ⟨Module.finrank ℂ (EuclideanSpace ℂ (Fin n)), rho, ?_⟩
  intro hrho
  apply hpi
  apply contRepresentationMatrixHom_injective_on_operators pi
  simpa [rho] using hrho

/-- Closed universal Peter--Weyl separation statement. -/
def CompactGroupsAreMatrixSeparated : Prop := SeparatesPoints.{u}

/-- The analytic Peter--Weyl input used by the five-radical theorem is now
proved inside the library. -/
theorem compactGroupsAreMatrixSeparated : CompactGroupsAreMatrixSeparated.{u} :=
  separatesPoints

end

end PeterWeyl
end GroupApproximation

#audit_closed_axioms GroupApproximation.PeterWeyl.compactGroupsAreMatrixSeparated
