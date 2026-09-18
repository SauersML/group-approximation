import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosedCounter
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.Closed
import GroupApproximation.Meta.AxiomGuard

/-!
# Closing Kasparov stabilization, lane `nm-tww-24`: endpoints

## Where stabilization and polar decomposition appear

A search of the formalization for open stabilization or polar-decomposition hypotheses
finds exactly one restated literature statement outside `TWWLanes/KasparovStab/`:
`HilbertModule.StabilizationInput` (`Analysis/CStarStabilization.lean`). No declaration
consumes it. `PolarUnitaryStatement` and `KasparovStabilizationStatement` are already
closed by `KasparovStab.polarUnitaryStatement_holds` and
`KasparovStab.kasparovStabilizationStatement_holds`. The other "polar" corrections in the
corpus are finite-dimensional and not Hilbert-module statements.

## Truth check (loud): `StabilizationInput` is FALSE

`StabilizationInput B` asks for `H_B ⊕ E ≅ H_B` for every countably generated `E`, with
no completeness hypothesis. It is **strictly stronger** than
`KasparovStabilizationStatement B`, and it is **false** for every nontrivial unital `B`:

* `stabilizationInput_iff_complete`: given the proved stabilization theorem,
  `StabilizationInput B` holds exactly when every countably generated module is complete.
* `not_stabilizationInput`: for nontrivial unital `B`, `c₀₀(B)` is countably generated
  and not complete, so `StabilizationInput B` fails.
* `stabilizationInput_iff_subsingleton`: for unital `B`, `StabilizationInput B` holds
  if and only if `B` is trivial.

## Closers

* `absorbs_of_isCompleteModule`: the corrected field of `StabilizationInput`, with
  `IsCompleteModule E` added, holds for every `B`.
* `stabilizationInput_of_subsingleton`: the literal field holds when `B` is trivial.

Both universes are `CStarModule.{v, v}`, so no universe bridge is needed.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovClosed

open GroupApproximation.HilbertModule GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

universe v

section NonUnital

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Kasparov stabilization, corrected field** (unconditional): `H_B ⊕ E ≅ H_B` for
countably generated, complete `E`. -/
theorem absorbs_of_isCompleteModule (E : CStarModule.{v, v} B)
    (hgen : IsCountablyGenerated E) (hE : IsCompleteModule E) :
    ∃ U : Adjointable (prod (standardModule ℕ B) E) (standardModule ℕ B), U.IsUnitaryAdj :=
  kasparovStabilizationStatement_holds (B := B) E hgen hE

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.absorbs_of_isCompleteModule

/-- **The exact gap of `StabilizationInput`**: it is equivalent to "countably generated
modules are complete". -/
theorem stabilizationInput_iff_complete :
    StabilizationInput B ↔
      ∀ E : CStarModule.{v, v} B, IsCountablyGenerated E → IsCompleteModule E :=
  ⟨fun h E hE => completeModule_of_stabilization E (h.absorbs E hE),
    fun h => ⟨fun E hE => absorbs_of_isCompleteModule E hE (h E hE)⟩⟩

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.stabilizationInput_iff_complete

/-- Over a trivial algebra every module is complete, since every vector is `0`. -/
theorem isCompleteModule_of_subsingleton [Subsingleton B] (E : CStarModule.{v, v} B) :
    IsCompleteModule E := by
  have h0 : ∀ x : E.carrier, x = 0 := fun x => E.inner_self_eq_zero x (Subsingleton.elim _ _)
  intro u _
  refine ⟨0, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  rw [(E.norm_eq_zero_iff _).mpr (h0 _)]
  exact hε.le

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.isCompleteModule_of_subsingleton

/-- `StabilizationInput` does hold over the zero algebra. -/
theorem stabilizationInput_of_subsingleton [Subsingleton B] : StabilizationInput B :=
  stabilizationInput_iff_complete.mpr fun E _ => isCompleteModule_of_subsingleton E

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.stabilizationInput_of_subsingleton

end NonUnital

section Unital

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **LOUD: `StabilizationInput` is false** for every nontrivial unital C⋆-algebra. -/
theorem not_stabilizationInput [Nontrivial B] : ¬ StabilizationInput B := fun h =>
  not_isCompleteModule_c00 (B := B)
    (stabilizationInput_iff_complete.mp h (c00 B) c00_isCountablyGenerated)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.not_stabilizationInput

/-- For unital `B`, `StabilizationInput B` holds exactly for the zero algebra. -/
theorem stabilizationInput_iff_subsingleton : StabilizationInput B ↔ Subsingleton B := by
  constructor
  · intro h
    by_contra hs
    haveI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hs
    exact not_stabilizationInput h
  · intro hs
    haveI := hs
    exact stabilizationInput_of_subsingleton

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.stabilizationInput_iff_subsingleton

end Unital

end KasparovClosed
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
