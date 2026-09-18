import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly
import GroupApproximation.GGT.HullSCTheorem71GeneralLeastArea
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFree.HullRouting.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:torsionfree`: routing an infinite normal subgroup onto a torsion-free quotient

`non_mf_group_notes.tex`, Theorem `thm:torsionfree`, l.2786-2799. Hull's Theorem 7.1 is applied
to Hull's alphabet, a finite generating family and a radius whose ball contains `F`.

HELD, NOT LANDED: the first import is lane GL06's assembly of Osin's Lemma 4.4 at least-area
diagrams (`Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea`). The module name and the
declaration name are provisional. Land this file after GL06 lands.
-/

namespace GroupApproximation.Full.NN07d

/-- **Hull's Theorem 7.1 routing** (`thm:torsionfree`, `non_mf_group_notes.tex` l.2786-2799). An
infinite normal subgroup `N` of a finitely generated, torsion-free, acylindrically hyperbolic
group maps onto a torsion-free quotient, by a surjection injective on a prescribed finite set. -/
theorem exists_routedQuotient {G : Type} [Group G] [Group.FG G]
    [GroupApproximation.Manuscript.NonMF.TorsionFree.IsAcylindricallyHyperbolic G]
    (hG : GroupApproximation.IsPowerTorsionFree G) (N : Subgroup G) [N.Normal]
    (hN : (N : Set G).Infinite) (F : Set G) (hF : F.Finite) :
    ∃ (Q : Type) (_ : Group Q) (q : G →* Q), Function.Surjective q ∧
      GroupApproximation.IsPowerTorsionFree Q ∧ N.map q = ⊤ ∧ Set.InjOn q F := by
  obtain ⟨A, m, t, R, hsuit, htop, hR⟩ := exists_routingParameters hG N hN hF
  obtain ⟨T⟩ :=
    HullSC.hullTowerStatementGeneral_of_leastAreaLeaves
      Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}
      HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed
      A hsuit (fun _ : Fin 0 => hsuit) t R
  exact routedQuotient_of_hullTower hG htop hR T

end GroupApproximation.Full.NN07d

#audit_axioms GroupApproximation.Full.NN07d.exists_routedQuotient
