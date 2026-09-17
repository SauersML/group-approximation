import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.PrintedHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFHostInstancesLamplighterClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:host`, last statement: one host for the recursively presented LEF groups

`simple_kazhdan_sofic_group.tex`, Corollary `cor:host` (l.463–470):

> So one such group contains every recursively presented finitely generated LEF group, for instance
> every finitely presented residually finite group and every `G_Y` with `L(Y)` recursive
> (Corollary `cor:wp`).

Proof (l.598–600): *The last statement of Corollary `cor:host` follows, as there are countably many
recursive presentations.*

## Spelling

* "Such a group" is `IsPrintedHost` (`PrintedHost.lean`).
* LEF is the printed definition `IsTextbookLEF`.
* "Recursively presented" is `Nonempty (Higman.RecursivePresentation Γ)`.
* "`G_Y` with `L(Y)` recursive": `G_Y = EL_3(R_Y)` for an infinite minimal subshift `Y` over a finite
  alphabet, whose language oracle `languageOracle Y` is partial recursive.

## Proof route

The closed corpus theorem `printedRecursivelyPresentedLEFHostInstances` gives a host `IsLEFHost E` with
all three embedding properties. `isPrintedHost_of_isLEFHost` turns it into a printed host.
-/

namespace GroupApproximation.Full.SK12

open SymbolicDynamics.FullShift

/-- **`cor:host`, last statement** (tex l.466–469): one such group `E` contains every recursively
presented finitely generated LEF group, every finitely presented residually finite group, and every
`G_Y` for an infinite minimal subshift `Y` with recursive language. -/
theorem corHost_recursivelyPresentedInstances :
    ∃ (E : Type) (_ : Group E), IsPrintedHost E ∧
      (∀ (Γ : Type) [Group Γ], Group.FG Γ → Nonempty (Higman.RecursivePresentation Γ) →
        IsTextbookLEF Γ → ∃ f : Γ →* E, Function.Injective f) ∧
      (∀ (Γ : Type) [Group Γ], Group.IsFinitelyPresented Γ → Group.ResiduallyFinite Γ →
        ∃ f : Γ →* E, Function.Injective f) ∧
      (∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
        [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier →
          GroupApproximation.SimpleKazhdanSofic.IsMinimal S →
          Partrec (GroupApproximation.SimpleKazhdanSofic.languageOracle S) →
          ∃ f : GroupApproximation.SimpleKazhdanSofic.G S →* E, Function.Injective f) := by
  obtain ⟨E, _, hE, hrec, hfp, hlang⟩ :=
    GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHostInstances
  exact ⟨E, inferInstance, isPrintedHost_of_isLEFHost hE,
    fun Γ _ hfg hrp hΓ => hrec Γ hfg hrp ((isLEF_iff_textbook Γ).2 hΓ), hfp, hlang⟩

#audit_axioms GroupApproximation.Full.SK12.corHost_recursivelyPresentedInstances

end GroupApproximation.Full.SK12
