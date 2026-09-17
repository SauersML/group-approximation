import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.ExpanderBridge
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.HyperlinearPrinted
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed endpoints of Lane 1 (`thm:main`, tex l.86–109)

`simple_kazhdan_sofic_group.tex`, the paragraphs after Theorem `thm:main` (gap report, Lane 1, items
D1, D2 and the M1 bridge).  Each claim is a closed proposition `…Statement` with a proof `…_holds`,
audited by `#audit_closed_axioms`.

* `LimitsOfFiniteGroupsAreLEFStatement` (tex l.104–105): *Limits of finite groups in the space of
  marked groups are LEF*, with `MarkedConverges` and `IsLEFPrinted` as printed.
* `ExpanderLimitsAreLEFStatement`: an expander limit of groups from any class is LEF.
* `PrintedSoficIffStatement`, `PrintedHyperlinearIffStatement` (tex l.105–109): the printed sofic
  and hyperlinear definitions are the corpus notions `IsSofic`, `IsHyperlinear`.
* `PrintedSoficHyperlinearStatement`: printed sofic groups are printed hyperlinear.
* `ExpanderFamilyBridgeStatement` (M1 bridge, tex l.92–100): a marked limit of an edge-expanding
  family from a class `C` is an expander limit of groups from `C` in the printed vertex sense.
-/

universe u

namespace GroupApproximation.Full.SK01

/-- **tex l.104–105.** *Limits of finite groups in the space of marked groups are LEF.* -/
def LimitsOfFiniteGroupsAreLEFStatement : Prop :=
  ∀ (m : ℕ) (Q : ℕ → Type) [∀ k, Group (Q k)] [∀ k, Finite (Q k)] (q : ∀ k, Fin m → Q k)
    (G : Type u) [Group G] (g : Fin m → G), MarkedConverges q g → IsLEFPrinted G

theorem limitsOfFiniteGroupsAreLEF_holds : LimitsOfFiniteGroupsAreLEFStatement.{u} := by
  intro _ _ _ _ q _ _ g h
  exact limitsOfFiniteGroupsAreLEFPrinted q g h

/-- `thm:main` ("So `G_X` is LEF"): an expander limit of groups from any class is LEF. -/
def ExpanderLimitsAreLEFStatement : Prop :=
  ∀ (C : ∀ (Q : Type) [Group Q], Prop) (G : Type u) [Group G],
    IsExpanderLimitOfClass C G → IsLEFPrinted G

theorem expanderLimitsAreLEF_holds : ExpanderLimitsAreLEFStatement.{u} := by
  intro _ _ _ h
  exact isLEFPrinted_of_isExpanderLimitOfClass h

/-- **tex l.105–109, sofic.** The printed definition of sofic groups is `IsSofic`. -/
def PrintedSoficIffStatement : Prop :=
  ∀ (G : Type u) [Group G], PrintedIsSofic G ↔ IsSofic G

theorem printedSoficIff_holds : PrintedSoficIffStatement.{u} := by
  intro _ _
  exact printedIsSofic_iff

/-- **tex l.105–109, hyperlinear.** The printed definition of hyperlinear groups is
`IsHyperlinear`. -/
def PrintedHyperlinearIffStatement : Prop :=
  ∀ (G : Type u) [Group G], PrintedIsHyperlinear G ↔ IsHyperlinear G

theorem printedHyperlinearIff_holds : PrintedHyperlinearIffStatement.{u} := by
  intro _ _
  exact printedIsHyperlinear_iff

/-- **tex l.105–109.** Printed sofic groups are printed hyperlinear. -/
def PrintedSoficHyperlinearStatement : Prop :=
  ∀ (G : Type u) [Group G], PrintedIsSofic G → PrintedIsHyperlinear G

theorem printedSoficHyperlinear_holds : PrintedSoficHyperlinearStatement.{u} := by
  intro _ _ h
  exact printedIsHyperlinear_of_printedIsSofic h

/-- **M1 bridge (tex l.92–100).** A marked limit `(G, s)` of an edge-expanding family `(H ℓ, σ ℓ)`
of groups from a class `C` is an expander limit of groups from `C` in the printed vertex sense. -/
def ExpanderFamilyBridgeStatement : Prop :=
  ∀ (C : ∀ (Q : Type) [Group Q], Prop) (ι : Type u) (G : Type u) [Group G] (s : ι → G)
    (H : ℕ → Type) [∀ ℓ, Group (H ℓ)] (σ : ∀ ℓ, ι → H ℓ), (∀ ℓ, C (H ℓ)) →
    SimpleKazhdanSofic.IsMarkedLimit s σ → SimpleKazhdanSofic.IsExpanderFamily σ →
    IsExpanderLimitOfClass C G

theorem expanderFamilyBridge_holds : ExpanderFamilyBridgeStatement.{u} := by
  intro _ _ _ _ _ _ _ _ hC hlim hexp
  exact isExpanderLimitOfClass_of_markedLimit_expanderFamily hC hlim hexp

end GroupApproximation.Full.SK01

#audit_closed_axioms GroupApproximation.Full.SK01.limitsOfFiniteGroupsAreLEF_holds
#audit_closed_axioms GroupApproximation.Full.SK01.expanderLimitsAreLEF_holds
#audit_closed_axioms GroupApproximation.Full.SK01.printedSoficIff_holds
#audit_closed_axioms GroupApproximation.Full.SK01.printedHyperlinearIff_holds
#audit_closed_axioms GroupApproximation.Full.SK01.printedSoficHyperlinear_holds
#audit_closed_axioms GroupApproximation.Full.SK01.expanderFamilyBridge_holds
