import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.Predicates
import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-14, part 2: the upstream interfaces used by the reduction

The reduction chain is

```text
nm-tww-13 (τ amenable) → nm-tww-06 (θ into ∏_ω M_{X n}) → h (Φ into the corona)
  → nm-tww-09 (τ quasidiagonal).
```

Lane `nm-tww-09` is on disk. Its criterion
`LiftCriterion.isQuasidiagonalTrace_of_traceKernelLift_of_coronaUCPCoordinates` rests on the
Choi--Effros interface `LiftCriterion.CoronaUCPCoordinatesStatement` of lane `nm-tww-08`, and
`Reduction.lean` imports and uses both.

Lanes `nm-tww-06` and `nm-tww-13` are written in parallel and publish no interface on disk.
Following the author brief, their interfaces are recorded here as propositions that are
asserted nowhere.

## Truth check of the `nm-tww-06` interface (correction)

The lane prints this step as `IsAmenableTrace τ → ∃ θ, trace-compatible`. **As printed
it is false.** `Quasidiagonal.AmenableTraceModel` allows empty finite models, and
`normTrace` of the empty matrix algebra is `0`. So `τ = 0` is an amenable trace. A unital
`θ` into a tracial ultraproduct over nonempty models has `ultratrace (θ 1) = 1 ≠ 0`.
The corrected interface `AmenableUltraHomStatement` adds the hypothesis `τ 1 = 1`. It holds
for every tracial state, and in particular for `FaithfulTracialState`.

With `τ 1 = 1`, the trace clause at `1` makes the models nonempty from some index `N` on.
Reindex by `n ↦ n + N`. Take the class of the bounded sequence `(φₙ(a))ₙ` along any
nonprincipal ultrafilter, which is bounded because ucp maps are contractive. It is linear,
unital and `⋆`-preserving, because positive maps are self-adjoint. It is multiplicative,
because the Hilbert--Schmidt defects tend to zero. Its ultratrace is `lim_ω tr(φₙ(a)) = τ(a)`.
So the corrected interface is true.

## Truth check of the `nm-tww-13` interface

`NuclearAmenableTraceStatement` is the separable case of the repository input
`QuasidiagonalMF.NuclearAmenableTraceInput`. It is proved from that input below, so it is
no stronger. It is true: on a separable nuclear C⋆-algebra every tracial state is amenable
(Connes, Haagerup; Brown--Ozawa, Theorem 6.2.7), and separability is what turns local
models into one sequence.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace TraceKernelInterface

noncomputable section

universe u

/-- **Interface of lane `nm-tww-13`** (nuclear implies amenable). Every faithful tracial
state on a separable nuclear C⋆-algebra is an amenable trace. -/
def NuclearAmenableTraceStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A],
    CStarExactness.IsNuclearCStarAlgebra A →
      ∀ τ : FaithfulTracialState A, Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.NuclearAmenableTraceStatement

/-- The repository input `QuasidiagonalMF.NuclearAmenableTraceInput`, which has no
separability hypothesis, gives the `nm-tww-13` interface. -/
theorem nuclearAmenableTraceStatement_of_input
    (h : QuasidiagonalMF.NuclearAmenableTraceInput.{u}) :
    NuclearAmenableTraceStatement.{u} := by
  intro A _ _ hnuc τ
  exact h.amenableTrace A inferInstance hnuc τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.nuclearAmenableTraceStatement_of_input

/-- **Interface of lane `nm-tww-06`** (corrected with `τ 1 = 1`; see the module docstring).
A unital amenable trace has a trace-compatible unital `⋆`-homomorphism into a tracial matrix
ultraproduct over nonempty finite models. -/
def AmenableUltraHomStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (τ : A → ℂ),
    τ 1 = 1 → Quasidiagonal.IsAmenableTrace τ → HasTraceCompatibleUltraHom τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.AmenableUltraHomStatement

/-- **The faithful-trace chain `nm-tww-13 → nm-tww-06`.** On a separable nuclear C⋆-algebra,
every faithful tracial state has a trace-compatible homomorphism into a tracial matrix
ultraproduct. This is the hypothesis `θ` of the lifting interface. -/
theorem hasTraceCompatibleUltraHom_of_nuclear
    (hAmenable : NuclearAmenableTraceStatement.{u})
    (hUltra : AmenableUltraHomStatement.{u})
    {A : Type u} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A) (τ : FaithfulTracialState A) :
    HasTraceCompatibleUltraHom (fun a : A ↦ τ a) :=
  hUltra A (fun a : A ↦ τ a) (FaithfulTracialState.apply_one τ) (hAmenable A hnuc τ)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.hasTraceCompatibleUltraHom_of_nuclear

end

end TraceKernelInterface
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
