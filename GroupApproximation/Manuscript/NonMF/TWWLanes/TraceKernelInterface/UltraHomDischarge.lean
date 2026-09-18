import GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.Reduction
import GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-30: the `nm-tww-06` interface `AmenableUltraHomStatement`, proved

`UpstreamStatements.lean` records the `nm-tww-06` step as the proposition
`AmenableUltraHomStatement` (asserted nowhere): a normalized (`τ 1 = 1`) amenable trace has a
trace-compatible unital `⋆`-homomorphism into a tracial matrix ultraproduct over nonempty
finite models.

**Endpoint.** `ultraHom_amenableUltraHomStatement : AmenableUltraHomStatement.{u}`, proved
outright, with no hypothesis.

## Truth check

The statement is true (the correction `τ 1 = 1` of `UpstreamStatements.lean` is necessary
and already present). No amenable group or Følner set enters: amenability of the *trace*
means ucp matrix models that are asymptotically multiplicative in `‖·‖₂` with traces tending
to `τ`, and the ultraproduct construction is direct.

## Proof

The on-disk lane `TWWLanes/AmenableUltraHom` proves
`AmenableUltraHom.exists_tracialQuotientHom_of_isAmenableTrace`: from
`IsAmenableTrace τ` and `τ 1 = 1` it produces nonempty models `X`, a free ultrafilter `ω`
and `θ : A →⋆ₐ[ℂ] TracialMatrixQuotient X ω` with `ultratraceCLM X ω (θ a) = τ a`.
Its route: drop the finitely many empty models (`exists_tail_card_pos`), take the class of
the bounded sequence `(φ_{n+N} a)_n` (`tailHom`), and compute the ultratrace as the
ultralimit of `tr(φ_{n+N} a) → τ a`. The only change here is to forget the cofinite bound
and to cross from `ultratraceCLM` to `ultratrace` by `ultratraceCLM_apply` (`rfl`).

As corollaries, the `nm-tww-06` hypothesis `hUltra` is dropped from the chain
`hasTraceCompatibleUltraHom_of_nuclear` and from the reduction
`tikuisisWhiteWinterStatement_of_traceKernelLift`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace TraceKernelInterface

noncomputable section

universe u

/-- **The `nm-tww-06` interface holds.** Every normalized amenable trace has a
trace-compatible unital `⋆`-homomorphism into a tracial matrix ultraproduct over nonempty
finite models. -/
theorem ultraHom_amenableUltraHomStatement : AmenableUltraHomStatement.{u} := by
  intro A _ τ hone hτ
  obtain ⟨X, hXne, ω, -, θ, hθ⟩ :=
    AmenableUltraHom.exists_tracialQuotientHom_of_isAmenableTrace hτ hone
  letI : ∀ n, Nonempty (X n) := hXne
  exact ⟨X, hXne, ω, θ, fun a ↦
    (TracialUltraproduct.ultratraceCLM_apply X ω (θ a)).symm.trans (hθ a)⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.ultraHom_amenableUltraHomStatement

/-- **The faithful-trace chain `nm-tww-13 → nm-tww-06`, without the `nm-tww-06`
hypothesis.** -/
theorem ultraHom_hasTraceCompatibleUltraHom_of_nuclear
    (hAmenable : NuclearAmenableTraceStatement.{u})
    {A : Type u} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A) (τ : FaithfulTracialState A) :
    HasTraceCompatibleUltraHom (fun a : A ↦ τ a) :=
  hasTraceCompatibleUltraHom_of_nuclear hAmenable ultraHom_amenableUltraHomStatement hnuc τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.ultraHom_hasTraceCompatibleUltraHom_of_nuclear

/-- **Tikuisis--White--Winter from trace-kernel extension lifting, without the `nm-tww-06`
hypothesis.** The remaining hypotheses are `nm-tww-13`, `nm-tww-08` and the lifting
interface `h` (sibling lane `nm-tww-31`). -/
theorem ultraHom_tikuisisWhiteWinterStatement_of_traceKernelLift {T : KK.KasparovTheory.{u}}
    (hAmenable : NuclearAmenableTraceStatement.{u})
    (hChoiEffros : LiftCriterion.CoronaUCPCoordinatesStatement.{u})
    (h : TraceKernelLiftStatement.{u} (KK.KasparovTheory.SatisfiesUCT T)) :
    RelatedTWW.TikuisisWhiteWinterStatement T :=
  tikuisisWhiteWinterStatement_of_traceKernelLift hAmenable
    ultraHom_amenableUltraHomStatement hChoiEffros h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.ultraHom_tikuisisWhiteWinterStatement_of_traceKernelLift

end

end TraceKernelInterface
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
