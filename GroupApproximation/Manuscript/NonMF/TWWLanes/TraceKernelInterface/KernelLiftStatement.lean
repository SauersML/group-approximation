import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.KernelLiftCorona
import GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.Statement
import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.Interface
import GroupApproximation.Manuscript.NonMF.RelatedTWW.Definitions
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-31, part 2: the lifting interface is its quasidiagonal form

`TraceKernelLiftStatement UCT` is not proved here. At `RelatedTWW.trivialKasparovTheory` it
is the open UCT-free Tikuisis--White--Winter question (`Reduction.lean`), so it cannot be proved
for an arbitrary predicate `UCT`.

This file isolates `KernelLiftQuasidiagonalStatement UCT`. It has the same hypotheses as the
lifting interface, and its conclusion is that `τ` is a **quasidiagonal trace**, not that a
trace-compatible corona homomorphism exists.

## LOUD: the isolated statement is EQUIVALENT to the target, not strictly weaker

Both directions are proved, and neither has a hypothesis:

* `kernelLift_traceKernelLiftStatement_of_quasidiagonal` (the `_of_` reduction). Quasidiagonal
  models give the corona homomorphism (`KernelLiftCorona.lean`).
* `kernelLiftQuasidiagonalStatement_of_traceKernelLift`. A trace-compatible corona homomorphism
  on a separable nuclear algebra makes `τ` quasidiagonal (lane `nm-tww-09`, over the proved
  Choi--Effros interface `CoronaChoiEffros.coronaUCPCoordinatesStatement`).

So `kernelLiftQuasidiagonalStatement_iff` holds for **every** `UCT`. The statement is
**logically equivalent** to `TraceKernelLiftStatement UCT`. It is smaller only in proof
content: the corona construction and the trace computation are discharged, and what remains is
the bare quasidiagonality claim.

## Truth check

* At Kasparov's genuine `KK`, `KernelLiftQuasidiagonalStatement T.SatisfiesUCT` is **true**. It
  follows from Tikuisis--White--Winter (Annals 2017) by dropping the hypothesis `θ`
  (`kernelLiftQuasidiagonalStatement_of_tikuisisWhiteWinter`).
* At `RelatedTWW.trivialKasparovTheory` it is **open**, like the target, because the two are
  equivalent.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace TraceKernelInterface

noncomputable section

universe u

/-- **The quasidiagonal form of the lifting interface (lane nm-tww-31).** Let `S` be separable,
nuclear and `UCT`, and let `τ` be a faithful tracial state on `S` with a trace-compatible
homomorphism into a tracial matrix ultraproduct. Then `τ` is a quasidiagonal trace.

**LOUD: this is EQUIVALENT to `TraceKernelLiftStatement UCT` for every `UCT`**
(`kernelLiftQuasidiagonalStatement_iff`). It is not strictly weaker. It is true at genuine `KK`
by Tikuisis--White--Winter, and open at `RelatedTWW.trivialKasparovTheory`. -/
def KernelLiftQuasidiagonalStatement (UCT : KK.SepCStarAlgebra.{u} → Prop) : Prop :=
  ∀ S : KK.SepCStarAlgebra.{u}, CStarExactness.IsNuclearCStarAlgebra S → UCT S →
    ∀ τ : FaithfulTracialState S,
      HasTraceCompatibleUltraHom (fun a : S ↦ τ a) →
        Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.KernelLiftQuasidiagonalStatement

/-- **The `_of_` reduction.** The quasidiagonal form gives the lifting interface. The corona
homomorphism is built from the quasidiagonal models (`kernelLiftCoronaHom`). -/
theorem kernelLift_traceKernelLiftStatement_of_quasidiagonal
    {UCT : KK.SepCStarAlgebra.{u} → Prop} (h : KernelLiftQuasidiagonalStatement UCT) :
    TraceKernelLiftStatement UCT := by
  intro S hnuc huct τ hθ
  exact kernelLift_hasTraceCompatibleCoronaHom_of_isQuasidiagonalTrace
    (FaithfulTracialState.apply_one τ) (h S hnuc huct τ hθ)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLift_traceKernelLiftStatement_of_quasidiagonal

/-- **The converse, unconditionally.** The lifting interface gives the quasidiagonal form,
through the lane `nm-tww-09` criterion over the proved Choi--Effros interface. -/
theorem kernelLiftQuasidiagonalStatement_of_traceKernelLift
    {UCT : KK.SepCStarAlgebra.{u} → Prop} (h : TraceKernelLiftStatement UCT) :
    KernelLiftQuasidiagonalStatement UCT := by
  intro S hnuc huct τ hθ
  obtain ⟨X, hne, ω, hω, Φ, htr⟩ := h S hnuc huct τ hθ
  letI : ∀ n, Nonempty (X n) := hne
  exact LiftCriterion.isQuasidiagonalTrace_of_traceKernelLift_of_coronaUCPCoordinates
    CoronaChoiEffros.coronaUCPCoordinatesStatement hnuc X ω hω Φ htr

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLiftQuasidiagonalStatement_of_traceKernelLift

/-- **LOUD: the isolated statement is equivalent to the target**, for every predicate `UCT`. -/
theorem kernelLiftQuasidiagonalStatement_iff {UCT : KK.SepCStarAlgebra.{u} → Prop} :
    KernelLiftQuasidiagonalStatement UCT ↔ TraceKernelLiftStatement UCT :=
  ⟨kernelLift_traceKernelLiftStatement_of_quasidiagonal,
    kernelLiftQuasidiagonalStatement_of_traceKernelLift⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLiftQuasidiagonalStatement_iff

/-- **Truth at a Kasparov theory.** Tikuisis--White--Winter for `T` gives the quasidiagonal form
at `T.SatisfiesUCT`, by dropping the hypothesis `θ`. -/
theorem kernelLiftQuasidiagonalStatement_of_tikuisisWhiteWinter {T : KK.KasparovTheory.{u}}
    (h : RelatedTWW.TikuisisWhiteWinterStatement T) :
    KernelLiftQuasidiagonalStatement (KK.KasparovTheory.SatisfiesUCT T) :=
  fun S hnuc huct τ _ ↦ h S hnuc huct τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLiftQuasidiagonalStatement_of_tikuisisWhiteWinter

/-- **Tikuisis--White--Winter implies the lifting interface**, with no other input. -/
theorem kernelLift_traceKernelLiftStatement_of_tikuisisWhiteWinter {T : KK.KasparovTheory.{u}}
    (h : RelatedTWW.TikuisisWhiteWinterStatement T) :
    TraceKernelLiftStatement (KK.KasparovTheory.SatisfiesUCT T) :=
  kernelLift_traceKernelLiftStatement_of_quasidiagonal
    (kernelLiftQuasidiagonalStatement_of_tikuisisWhiteWinter h)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.kernelLift_traceKernelLiftStatement_of_tikuisisWhiteWinter

end

end TraceKernelInterface
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
