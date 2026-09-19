import GroupApproximation.Analysis.FiniteTraceCompactness
import GroupApproximation.Analysis.TracialStateQuotient

/-!
# A corona trace from finite coordinate-state constraints

This file packages the compactness route to the rogue trace.  It avoids both
Jordan decomposition and Cuntz--Pedersen positive separation: states on the
bounded product solve finitely many tracial constraints and become arbitrarily
small on finitely many `c₀` elements.  Weak-star compactness produces a trace
annihilating the whole `c₀` ideal, which then descends to the norm corona.
-/

namespace GroupApproximation
namespace CoronaTraceCompactness

open Filter PolarLiftingGeneralCStar
open CStarState CuntzPedersenCoronaObstruction FiniteTraceCompactness

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- Finite state solvability on the bounded product produces a tracial state
on the `c₀` corona detecting the chosen bounded sequence. -/
theorem exists_corona_tracialState_of_finite_state_constraints
    (h : BoundedCStarSequence D)
    (hfinite : ∀ K : VanishingConstraintIndex
        (nullCStarSequenceIdeal D atTop : Set (BoundedCStarSequence D)),
      ∃ φ : State (BoundedCStarSequence D),
        φ.toCLM h = 1 ∧
        (∀ z ∈ K.commutators,
          φ.toCLM (selfCommutator z) = 0) ∧
        ∀ a ∈ K.vanishing,
          ‖φ.toCLM a.1‖ ≤ 1 / (K.precision + 1 : ℝ)) :
    ∃ σ : TracialState (CStarProductCorona D atTop),
      σ (cStarProductCoronaQuotient D atTop h) = 1 := by
  obtain ⟨tau, htauh, htauI⟩ :=
    exists_tracialState_annihilating_of_finite_state_constraints h
      (nullCStarSequenceIdeal D atTop : Set (BoundedCStarSequence D)) hfinite
  let sigma : TracialState (CStarProductCorona D atTop) :=
    tau.descend (nullCStarSequenceIdeal D atTop) (fun a ha ↦ htauI a ha)
  refine ⟨sigma, ?_⟩
  simpa [sigma, cStarProductCoronaQuotient_apply] using htauh

end

end CoronaTraceCompactness
end GroupApproximation
