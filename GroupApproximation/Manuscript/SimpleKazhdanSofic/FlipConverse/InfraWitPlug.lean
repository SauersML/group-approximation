import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonDisjWit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraDisplace
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraCommLocal
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonMetabBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-disjoint supports give a commutator witness, part 3: plugging in lanes 01, 02, 05

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Plug-in lane `sk-flip-18`.

Lane `sk-flip-07` (`InfraNonDisjWit`) proves the commutator witness from three interfaces
stated in `InfraNonDisjWitStatements`.  Two of them are now on disk and are discharged here:

* `nonDisjWitDisplacedStatement_holds`: `NonDisjWitDisplacedStatement` from lane `sk-flip-01`
  (`exists_isClopen_displaced_common`, same instance list `CompactSpace`, `T2Space`,
  `TotallyDisconnectedSpace`; no extra instance needed).
* `nonDisjWitCommLocalStatement_holds`: `NonDisjWitCommLocalStatement` from lane `sk-flip-02`
  (`commutator_commutator_eq_of_displaced`, only `TopologicalSpace` needed).

The third, `NonDisjWitNonMetabelianStatement`, is reduced by lane `sk-flip-05`
(`nonDisjWitNonMetabelian_of_towerPermEmbedding`) to `TowerPermEmbeddingStatement.{0}` (lane
`sk-flip-04` interface, proved concurrently elsewhere and kept as a hypothesis here).

Endpoint: `exists_commutator_witness_of_not_disjoint_of_towerPermEmbedding`, whose only
`Statement` hypothesis is `TowerPermEmbeddingStatement.{0}`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology
open scoped commutatorElement

/-- The lane `sk-flip-01` interface holds unconditionally. -/
theorem nonDisjWitDisplacedStatement_holds : NonDisjWitDisplacedStatement := by
  intro X _ _ _ _ f k x hf hk
  exact exists_isClopen_displaced_common hf hk

/-- The lane `sk-flip-02` interface holds unconditionally. -/
theorem nonDisjWitCommLocalStatement_holds : NonDisjWitCommLocalStatement := by
  intro X _ a b g W ha hb hW
  exact commutator_commutator_eq_of_displaced ha hb hW

/-- Non-disjoint moved sets in `[[T]]` give a nonvanishing commutator witness, for a minimal
homeomorphism of a Cantor space, from the tower-permutation interface alone. -/
theorem exists_commutator_witness_of_not_disjoint_of_towerPermEmbedding
    (h04 : TowerPermEmbeddingStatement.{0}) {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {f k : topologicalFullGroup T}
    (h : ¬ Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X))) :
    ∃ a b c d : topologicalFullGroup T, ⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ ≠ 1 :=
  exists_commutator_witness_of_not_disjoint_of_statements nonDisjWitDisplacedStatement_holds
    nonDisjWitCommLocalStatement_holds (nonDisjWitNonMetabelian_of_towerPermEmbedding h04) hT h

/-- Contrapositive form: if every double commutator `⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆` vanishes, the
moved sets of `f` and `k` are disjoint, from the tower-permutation interface alone. -/
theorem disjoint_movedSet_of_forall_commutator_eq_one_of_towerPermEmbedding
    (h04 : TowerPermEmbeddingStatement.{0}) {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {f k : topologicalFullGroup T}
    (hall : ∀ a b c d : topologicalFullGroup T, ⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ = 1) :
    Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) :=
  disjoint_movedSet_of_forall_commutator_eq_one_of_statements
    nonDisjWitDisplacedStatement_holds nonDisjWitCommLocalStatement_holds
    (nonDisjWitNonMetabelian_of_towerPermEmbedding h04) hT hall

/-- The universal `Statement` form of lane `sk-flip-07`, from the tower-permutation interface
alone. -/
theorem commutatorWitnessOfNotDisjoint_of_towerPermEmbedding
    (h04 : TowerPermEmbeddingStatement.{0}) : CommutatorWitnessOfNotDisjointStatement :=
  commutatorWitnessOfNotDisjoint_of_statements nonDisjWitDisplacedStatement_holds
    nonDisjWitCommLocalStatement_holds (nonDisjWitNonMetabelian_of_towerPermEmbedding h04)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.nonDisjWitDisplacedStatement_holds
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.nonDisjWitCommLocalStatement_holds
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_commutator_witness_of_not_disjoint_of_towerPermEmbedding
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.disjoint_movedSet_of_forall_commutator_eq_one_of_towerPermEmbedding
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.commutatorWitnessOfNotDisjoint_of_towerPermEmbedding
