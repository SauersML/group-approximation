import GroupApproximation.Analysis.LIXLimitWitness
import GroupApproximation.Analysis.LIXConnectingMap
import GroupApproximation.Meta.AxiomGuard

/-!
# The counterexample algebra for STW Problem LIX

Everything upstream of this file is generic: `Analysis/LIXLimitTower` and
`Analysis/LIXLimitCompletion` build the inductive limit of an *arbitrary* tower of unital
C⋆-algebras with injective connecting maps, and `Analysis/LIXLimitWitness` packages its
`K₁`-non-injectivity witness.  This file instantiates all of it at the one tower the problem is
about: the stage algebras `A_i = Γ(X_i, End E_i)` of `Analysis/LIXStageAlgebra` with the twisted
point-evaluation maps `φ_i` of `Analysis/LIXConnectingMap`.

The result, `LIXLimit`, is the algebra the endpoint quantifies over.  Two facts about it are
worth stating explicitly because they are the ones a universe or instance slip would silently
break, and both are checked below rather than asserted:

* `LIXLimit : Type`, i.e. universe `0`.  `ProblemLIX` quantifies over `Type`, so a limit landing
  in `Type 1` would answer a weaker question.  Nothing in the construction raises the universe:
  `Σ n, A n`, `Quotient` and `UniformSpace.Completion` all stay where the levels are.
* `CStarAlgebra LIXLimit` and `Nontrivial LIXLimit` resolve by instance search alone, the first
  through `CStarCompletion.completionCStarAlgebra` and the second from
  `STW59.instNontrivialStageAlgebra` at level `0`.

`LIXLimit` is an `abbrev`, so it is reducible and every instance of `lixTower.Limit` is found
for it without a transport layer.

## What is still hypothetical here

`lixLimit_hasK1InjWitness` takes the two properties of the generator as hypotheses: that it is
null-homotopic in no stage (manuscript Corollary 4 together with Lemma 6, lane `cs-clutching`)
and that `diag (u, 1)` is already null-homotopic over the base stage.  Neither is assumed
anywhere in this lane's own results; they are the interface `cs-clutching` fills.
-/

namespace GroupApproximation

namespace LIX

noncomputable section

/- The stage algebras are subtypes of `C(X_i, CStarMatrix ι ι ℂ)`, and that ambient carries a
*pointwise* `PartialOrder` inherited from `CStarMatrix.instPartialOrder`.  It reaches
`STW59.StageAlgebra i` through `Subtype.partialOrder` and shadows the spectral order, so
`StarOrderedRing` — which is stated relative to `CStarAlgebra.spectralOrder` — then fails to
synthesize and `CStarMat 2 (STW59.StageAlgebra k)` is not a `CStarAlgebra`.  Raising the
priority of the spectral pair fixes it, and keeps the *same* two constants the rest of the lane
uses, so no transport lemma is needed anywhere. -/
attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

example (k : ℕ) : CStarAlgebra (STW59.StageAlgebra k) := inferInstance
example (k : ℕ) : PartialOrder (STW59.StageAlgebra k) := inferInstance
example (k : ℕ) : StarOrderedRing (STW59.StageAlgebra k) := inferInstance
example (k : ℕ) : CStarAlgebra (CStarMat 2 (STW59.StageAlgebra k)) := inferInstance

/-- **The LIX tower**: the stage algebras of `Analysis/LIXStageAlgebra` with the connecting maps
of `Analysis/LIXConnectingMap`.  Unitality is free (`→⋆ₐ[ℂ]` is unital by definition) and
isometry is derived from injectivity, so `STW59.connect_injective` is the only input. -/
def lixTower : CStarTower STW59.StageAlgebra :=
  CStarTower.ofInjective STW59.connect STW59.connect_injective

@[simp] theorem lixTower_succHom (i : ℕ) : lixTower.succHom i = STW59.connect i := rfl

/-- **The counterexample algebra for STW Problem LIX**: the inductive limit of the tower. -/
abbrev LIXLimit : Type := lixTower.Limit

example : CStarAlgebra LIXLimit := inferInstance

example : Nontrivial LIXLimit := inferInstance

/-- The canonical map of the `i`-th stage into the counterexample algebra. -/
def lixIota (i : ℕ) : STW59.StageAlgebra i →⋆ₐ[ℂ] LIXLimit := lixTower.limIota i

theorem lixIota_injective (i : ℕ) : Function.Injective (lixIota i) :=
  lixTower.limIota_injective i

@[simp] theorem norm_lixIota (i : ℕ) (a : STW59.StageAlgebra i) : ‖lixIota i a‖ = ‖a‖ :=
  lixTower.norm_limIota i a

@[simp] theorem lixIota_connect (i : ℕ) (a : STW59.StageAlgebra i) :
    lixIota (i + 1) (STW59.connect i a) = lixIota i a :=
  lixTower.limIota_succHom i a

theorem dense_iUnion_lixStage :
    Dense (⋃ i, ((lixTower.stage i : StarSubalgebra ℂ LIXLimit) : Set LIXLimit)) :=
  lixTower.dense_iUnion_stage

/-- **The `K₁`-non-injectivity witness for the counterexample algebra.**  The two hypotheses are
exactly `cs-clutching`'s Corollary 4 with Lemma 6, and the null-homotopy of `diag (u, 1)` over
the base stage; the conclusion is the named predicate `cs-endpoint` consumes. -/
theorem lixLimit_hasK1InjWitness {k : ℕ} (u : unitary (STW59.StageAlgebra k))
    (hstage : ∀ (j : ℕ) (hj : k ≤ j),
      unitaryHom (lixTower.climbHom hj) u ∉ unitaryComponentOne (STW59.StageAlgebra j))
    (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 (STW59.StageAlgebra k))) :
    HasK1InjWitness LIXLimit :=
  CStarTower.hasK1InjWitness_limit lixTower u hstage hdiag

/-! ### Axiom audit

`#audit_axioms` fails the build when the transitive closure leaves the classical allowlist, so
these lines are gates, not log output.  `lixLimit_hasK1InjWitness` is conditional by design — it
consumes `cs-clutching`'s two facts about the generator — so it gets the plain audit rather than
`#audit_closed_axioms`. -/

#audit_axioms lixTower
#audit_axioms lixIota
#audit_axioms lixLimit_hasK1InjWitness

end

end LIX

end GroupApproximation
