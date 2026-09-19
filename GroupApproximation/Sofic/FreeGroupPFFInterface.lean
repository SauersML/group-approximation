import GroupApproximation.Sofic.MFRepresentationVariants

/-!
# The exact Bordenave--Collins interface for finite-rank free groups

The repository's LEF and residual-finiteness models provide finite
permutation data, but they do not prove convergence to reduced operator norms.
This file separates the elementary finite-representation and trace data from
that one analytic input.

No Bordenave--Collins theorem is postulated here.  The only unconditional
result says that a supplied reduced-norm limit upgrades the displayed finite
trace models to `IsPFF`.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

/-- Genuine finite-image matrix representations of a finite-rank free group
whose normalized characters converge to the regular character.  Reduced-norm
convergence is deliberately absent. -/
structure FreeGroupFiniteTraceModels (rank : ℕ) where
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  representation : ∀ n,
    FreeGroup (Fin rank) →* Matrix.unitaryGroup (model n) ℂ
  traceConverges : ∀ g : FreeGroup (Fin rank),
    Tendsto
      (fun n ↦ normTrace (model n)
        (representation n g : Matrix (model n) (model n) ℂ))
      Filter.atTop
      (nhds (regularCharacter g))
  finiteImage : ∀ n,
    Set.Finite (Set.range fun g : FreeGroup (Fin rank) ↦ representation n g)

namespace FreeGroupFiniteTraceModels

/-- The precise strong-norm assertion supplied by the
Bordenave--Collins random-permutation theorem after diagonal selection. -/
def HasReducedNormLimit {rank : ℕ}
    (A : FreeGroupFiniteTraceModels rank) : Prop :=
  ∀ c : FreeGroup (Fin rank) →₀ ℂ,
    Tendsto
      (fun n ↦ ‖matrixGroupRingEvaluation A.model
        (fun k g ↦ A.representation k g) n c‖)
      Filter.atTop
      (nhds ‖reducedGroupRingEvaluation
        (G := FreeGroup (Fin rank)) c‖)

/-- Once the strong reduced-norm limit is supplied, the finite trace models
are exactly a PFF approximation. -/
noncomputable def toPFFApproximation {rank : ℕ}
    (A : FreeGroupFiniteTraceModels rank) (h : A.HasReducedNormLimit) :
    PFFApproximation (FreeGroup (Fin rank)) where
  model := A.model
  modelNonempty := A.modelNonempty
  representation := A.representation
  reducedNormConverges := by simpa [HasReducedNormLimit] using h
  traceConverges := A.traceConverges
  finiteImage := A.finiteImage

end FreeGroupFiniteTraceModels

/-- Statement-level Bordenave--Collins bridge.  This theorem has no hidden
literature axiom: both the finite trace models and their reduced-norm limit are
explicit arguments. -/
theorem isPFF_freeGroup_of_finiteTraceModels {rank : ℕ}
    (A : FreeGroupFiniteTraceModels rank) (h : A.HasReducedNormLimit) :
    IsPFF (FreeGroup (Fin rank)) :=
  ⟨A.toPFFApproximation h⟩

end GroupApproximation
