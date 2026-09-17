import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.UpstreamStatements
import GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.Statement
import GroupApproximation.Manuscript.NonMF.RelatedTWW.KasparovDegenerate
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-14, part 3: the Tikuisis--White--Winter reduction to trace-kernel lifting

**Endpoint.** `tikuisisWhiteWinterStatement_of_traceKernelLift` derives
`RelatedTWW.TikuisisWhiteWinterStatement T` from the lifting interface
`TraceKernelLiftStatement T.SatisfiesUCT`. It follows the chain

```text
τ faithful trace on S separable nuclear
  →(nm-tww-13) τ amenable
  →(nm-tww-06) θ : S → ∏_ω M_{X n}, trω ∘ θ = τ
  →(h, at T)   Φ : S → ℓ∞(M_{X' n}) / c₀(M_{X' n}), trω' ∘ π_ω' ∘ Φ = τ
  →(nm-tww-09 over nm-tww-08) τ quasidiagonal.
```

The upstream steps are the interfaces `NuclearAmenableTraceStatement`,
`AmenableUltraHomStatement` (corrected with `τ 1 = 1`), and the on-disk Choi--Effros interface
`LiftCriterion.CoronaUCPCoordinatesStatement`. All three are true standard theorems. See
`UpstreamStatements.lean` and `LiftCriterion/Statement.lean`.

**Where the gap is.** At the degenerate model `RelatedTWW.trivialKasparovTheory`, every
separable algebra satisfies the UCT. There the hypothesis `h` is the UCT-free lifting
statement, and the reduction turns it into quasidiagonality of every faithful trace on
every separable nuclear C⋆-algebra, the UCT-free Tikuisis--White--Winter question. **That
question is open.** So `h` at `trivialKasparovTheory` is an open problem, and it can only be
discharged at a real `KK` (Kasparov's theory, where the UCT hypothesis has content). See
`quasidiagonalTrace_of_traceKernelLift_trivialKasparovTheory`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace TraceKernelInterface

noncomputable section

universe u

/-- **Tikuisis--White--Winter from trace-kernel extension lifting (lane nm-tww-14).**
Let `T` be a Kasparov theory. Assume the lifting interface at `T.SatisfiesUCT` and the
upstream interfaces (`nm-tww-13` nuclear ⇒ amenable, `nm-tww-06` amenable ⇒ tracial
ultraproduct homomorphism, `nm-tww-08` Choi--Effros coordinates). Then every faithful
tracial state on a separable nuclear C⋆-algebra satisfying the UCT for `T` is
quasidiagonal.

At `RelatedTWW.trivialKasparovTheory` the hypothesis `h` is an **open problem** (the
UCT-free lifting statement). It can only be discharged at a real `KK`. -/
theorem tikuisisWhiteWinterStatement_of_traceKernelLift {T : KK.KasparovTheory.{u}}
    (hAmenable : NuclearAmenableTraceStatement.{u})
    (hUltra : AmenableUltraHomStatement.{u})
    (hChoiEffros : LiftCriterion.CoronaUCPCoordinatesStatement.{u})
    (h : TraceKernelLiftStatement.{u} (KK.KasparovTheory.SatisfiesUCT T)) :
    RelatedTWW.TikuisisWhiteWinterStatement T := by
  intro S hnuc huct τ
  obtain ⟨X, hne, ω, hω, Φ, htr⟩ :=
    h S hnuc huct τ (hasTraceCompatibleUltraHom_of_nuclear hAmenable hUltra hnuc τ)
  letI : ∀ n, Nonempty (X n) := hne
  exact LiftCriterion.isQuasidiagonalTrace_of_traceKernelLift_of_coronaUCPCoordinates
    hChoiEffros hnuc X ω hω Φ htr

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.tikuisisWhiteWinterStatement_of_traceKernelLift

/-- The same reduction, with the conclusion in the `QuasidiagonalMF` form
`TikuisisWhiteWinterTheorem T`. -/
theorem tikuisisWhiteWinterTheorem_of_traceKernelLift {T : KK.KasparovTheory.{u}}
    (hAmenable : NuclearAmenableTraceStatement.{u})
    (hUltra : AmenableUltraHomStatement.{u})
    (hChoiEffros : LiftCriterion.CoronaUCPCoordinatesStatement.{u})
    (h : TraceKernelLiftStatement.{u} (KK.KasparovTheory.SatisfiesUCT T)) :
    QuasidiagonalMF.TikuisisWhiteWinterTheorem T :=
  (RelatedTWW.tikuisisWhiteWinterStatement_iff T).mp
    (tikuisisWhiteWinterStatement_of_traceKernelLift hAmenable hUltra hChoiEffros h)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.tikuisisWhiteWinterTheorem_of_traceKernelLift

/-- **At the degenerate model the lifting interface loses its UCT hypothesis.** -/
theorem traceKernelLiftStatement_trivialKasparovTheory_iff :
    TraceKernelLiftStatement.{0}
        (KK.KasparovTheory.SatisfiesUCT RelatedTWW.trivialKasparovTheory.{0}) ↔
      ∀ S : KK.SepCStarAlgebra.{0}, CStarExactness.IsNuclearCStarAlgebra S →
        ∀ τ : FaithfulTracialState S,
          HasTraceCompatibleUltraHom (fun a : S ↦ τ a) →
            HasTraceCompatibleCoronaHom (fun a : S ↦ τ a) :=
  ⟨fun h S hnuc τ ↦ h S hnuc (RelatedTWW.satisfiesUCT_trivialKasparovTheory S) τ,
    fun h ↦ by
      intro S hnuc _ τ
      exact h S hnuc τ⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.traceKernelLiftStatement_trivialKasparovTheory_iff

/-- **The lifting interface at the degenerate model gives the open UCT-free statement.**
Together with the upstream interfaces, `h` at `RelatedTWW.trivialKasparovTheory` makes every
faithful tracial state on every separable nuclear C⋆-algebra quasidiagonal. That is the
UCT-free Tikuisis--White--Winter question, and it is **open**. So the hypothesis `h` here is
an open problem and is not expected to be discharged; the lifting interface can only be
discharged at a real `KK`. -/
theorem quasidiagonalTrace_of_traceKernelLift_trivialKasparovTheory
    (hAmenable : NuclearAmenableTraceStatement.{0})
    (hUltra : AmenableUltraHomStatement.{0})
    (hChoiEffros : LiftCriterion.CoronaUCPCoordinatesStatement.{0})
    (h : TraceKernelLiftStatement.{0}
      (KK.KasparovTheory.SatisfiesUCT RelatedTWW.trivialKasparovTheory.{0})) :
    ∀ S : KK.SepCStarAlgebra.{0}, CStarExactness.IsNuclearCStarAlgebra S →
      ∀ τ : FaithfulTracialState S,
        Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a) :=
  RelatedTWW.tikuisisWhiteWinterStatement_trivialKasparovTheory_iff.mp
    (tikuisisWhiteWinterStatement_of_traceKernelLift hAmenable hUltra hChoiEffros h)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.quasidiagonalTrace_of_traceKernelLift_trivialKasparovTheory

end

end TraceKernelInterface
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
