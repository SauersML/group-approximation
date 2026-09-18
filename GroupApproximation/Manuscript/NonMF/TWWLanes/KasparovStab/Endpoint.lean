import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.DenseT
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.ProdComplete
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: endpoint

## Truth check (loud)

The corpus field `HilbertModule.StabilizationInput.absorbs` reads "`H_B ⊕ E ≅ H_B` for every
countably generated `E`". **As stated it is false**, because a corpus `CStarModule` need
not be complete. A unitary `H_B ⊕ E → H_B` makes `E` complete
(`completeModule_of_stabilization`), and for `B ≠ 0` the finitely supported sequences
`c₀₀(B)` are countably generated and not complete. The corrected statement is
`KasparovStabilizationStatement`, which adds `IsCompleteModule E`.

## What is proved

`kasparovStabilization_of_polarUnitary`: the corrected Kasparov stabilization theorem
follows from `PolarUnitaryStatement`. For a generating sequence `x` of a complete `E`, the
Mingo--Phillips operator `T = mingoPhillips hE x : H_B ⊕ E → H_B` is adjointable, and
both `T` and `T⋆` have dense range (`hasDenseRange_mingoPhillips` and
`hasDenseRange_adjoint_mingoPhillips`). Both modules are complete.

## The remaining gap: `PolarUnitaryStatement`

"If `T : E → F` is adjointable between complete modules and `T`, `T⋆` have dense range,
then `E ≅ F` unitarily." This is Lance, *Hilbert C⋆-modules*, Prop. 3.8. The unitary is
the phase of the polar decomposition `T = U |T|`.

* **True.** For `|T| = (T⋆T)^{1/2}`, the map `|T| x ↦ T x` is isometric
  (`⟨Tx, Tx⟩ = ⟨|T|x, |T|x⟩`). Its domain `range |T| ⊇ range T⋆T` is dense because `T` and
  `T⋆` have dense range, and its range `range T` is dense. By completeness it extends
  to a surjective isometric `B`-module map `U : E → F`, which is unitary
  (Lance, Thm. 3.5).
* **Strictly smaller in proof content.** It is one functional-calculus step about a single
  operator. It knows nothing about generating sequences, `H_B`, or the construction of
  `T`, which is the whole of the Mingo--Phillips argument proved here. It is not
  equivalent to the target, since it concerns arbitrary pairs `E`, `F`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule

universe v

/-- **Kasparov stabilization, corrected**: `H_B ⊕ E ≅ H_B` for countably generated, complete
`E`. -/
def KasparovStabilizationStatement (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : Prop :=
  ∀ E : CStarModule.{v, v} B, IsCountablyGenerated E → IsCompleteModule E →
    ∃ U : Adjointable (prod (standardModule ℕ B) E) (standardModule ℕ B), U.IsUnitaryAdj

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.KasparovStabilizationStatement

/-- **Lance, Prop. 3.8**: an adjointable map between complete modules whose range and
adjoint range are dense has a unitary phase. -/
def PolarUnitaryStatement (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : Prop :=
  ∀ (E F : CStarModule.{v, v} B) (T : Adjointable E F), IsCompleteModule E →
    IsCompleteModule F → HasDenseRange T → HasDenseRange (Adjointable.adjoint T) →
    ∃ U : Adjointable E F, U.IsUnitaryAdj

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.PolarUnitaryStatement

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Kasparov stabilization from the polar unitary.** -/
theorem kasparovStabilization_of_polarUnitary (h : PolarUnitaryStatement B) :
    KasparovStabilizationStatement B := by
  intro E hgen hE
  obtain ⟨x, hx⟩ := hgen
  exact h (prod (standardModule ℕ B) E) (standardModule ℕ B) (mingoPhillips hE x)
    (isCompleteModule_prod isCompleteModule_standard hE) isCompleteModule_standard
    (hasDenseRange_mingoPhillips hE x) (hasDenseRange_adjoint_mingoPhillips hE x hx)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.kasparovStabilization_of_polarUnitary

/-- **Completeness is necessary**: a stabilization unitary forces `E` to be complete. -/
theorem completeModule_of_stabilization (E : CStarModule.{v, v} B)
    (hU : ∃ U : Adjointable (prod (standardModule ℕ B) E) (standardModule ℕ B),
      U.IsUnitaryAdj) :
    IsCompleteModule E := by
  obtain ⟨U, hU⟩ := hU
  exact isCompleteModule_of_unitary U hU isCompleteModule_standard

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.completeModule_of_stabilization

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
