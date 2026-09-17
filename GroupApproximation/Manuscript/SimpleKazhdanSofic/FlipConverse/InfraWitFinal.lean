import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraWitPlug
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraTowerPermStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Commutator witness for non-disjoint supports: unconditional form

Lanes `sk-flip-04`, `sk-flip-17` and `sk-flip-18`.

Lane 18 (`InfraWitPlug.lean`) reduces the commutator witness to
`TowerPermEmbeddingStatement.{0}`.  Lane 04 (`InfraTowerPermStatement.lean`) proves that
Statement as `towerPermEmbeddingStatement_holds`.  Plugging one into the other gives the
unconditional endpoints below.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open scoped commutatorElement

/-- If the moved sets of `f` and `k` meet, some iterated commutator of `f` and `k` is
nontrivial. -/
theorem exists_commutator_witness_of_not_disjoint {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {f k : topologicalFullGroup T}
    (h : ¬ Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X))) :
    ∃ a b c d : topologicalFullGroup T, ⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ ≠ 1 :=
  exists_commutator_witness_of_not_disjoint_of_towerPermEmbedding
    towerPermEmbeddingStatement_holds.{0} hT h

/-- If all these iterated commutators of `f` and `k` vanish, their moved sets are disjoint. -/
theorem disjoint_movedSet_of_forall_commutator_eq_one {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {f k : topologicalFullGroup T}
    (hall : ∀ a b c d : topologicalFullGroup T, ⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ = 1) :
    Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) :=
  disjoint_movedSet_of_forall_commutator_eq_one_of_towerPermEmbedding
    towerPermEmbeddingStatement_holds.{0} hT hall

/-- The universal `Statement` form of lane `sk-flip-07` holds. -/
theorem commutatorWitnessOfNotDisjointStatement_holds :
    CommutatorWitnessOfNotDisjointStatement :=
  commutatorWitnessOfNotDisjoint_of_towerPermEmbedding towerPermEmbeddingStatement_holds.{0}

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_commutator_witness_of_not_disjoint
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.disjoint_movedSet_of_forall_commutator_eq_one
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.commutatorWitnessOfNotDisjointStatement_holds
