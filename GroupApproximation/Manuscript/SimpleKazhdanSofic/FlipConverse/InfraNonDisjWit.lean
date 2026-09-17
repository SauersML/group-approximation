import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraNonDisjWitStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-disjoint supports give a commutator witness, part 2: the reduction

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Infrastructure lane `sk-flip-07`.

For a minimal homeomorphism `T` of a Cantor space and `f, k ∈ [[T]]` whose moved sets meet,
there are `a, b, c, d ∈ [[T]]` with `⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ ≠ 1`
(`exists_commutator_witness_of_not_disjoint_of_statements`); contrapositively, if all these double
commutators vanish then the moved sets are disjoint
(`disjoint_movedSet_of_forall_commutator_eq_one_of_statements`).

Route.  Take `x` moved by `f` and by `k`.  Lane 01 gives a clopen `W ∋ x` with `W ∩ f W = ∅` and
`W ∩ k W = ∅`.  Lane 05 gives `a, b, c, d ∈ [[T]]` supported in `W` with `⁅⁅a, b⁆, ⁅c, d⁆⁆ ≠ 1`.
Lane 02 rewrites `⁅⁅a, f⁆, b⁆ = ⁅a, b⁆` and `⁅⁅c, k⁆, d⁆ = ⁅c, d⁆` (in `X ≃ₜ X`, then in the
subgroup `[[T]]` by injectivity of the coercion).

Only this direction is true (carto note N4): disjointness of moved sets does NOT force all these
double commutators to vanish, since the support of `⁅a, f⁆` spreads to `a (movedSet f)`.

The three upstream lanes are not yet on disk; they enter as the `Statement`s of
`InfraNonDisjWitStatements`, all of which are true (reasons recorded there).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Non-disjoint moved sets in `[[T]]` give a nonvanishing commutator witness, for a minimal
homeomorphism of a Cantor space. -/
def CommutatorWitnessOfNotDisjointStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X), IsMinimalHomeo T →
      ∀ f k : topologicalFullGroup T,
        ¬ Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) →
          ∃ a b c d : topologicalFullGroup T, ⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ ≠ 1

/-- Lane `sk-flip-07`: non-disjoint moved sets give a commutator witness, from the interfaces of
lanes 01, 02 and 05. -/
theorem exists_commutator_witness_of_not_disjoint_of_statements
    (h01 : NonDisjWitDisplacedStatement) (h02 : NonDisjWitCommLocalStatement)
    (h05 : NonDisjWitNonMetabelianStatement) {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {f k : topologicalFullGroup T}
    (h : ¬ Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X))) :
    ∃ a b c d : topologicalFullGroup T, ⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ ≠ 1 := by
  obtain ⟨x, hxf, hxk⟩ := Set.not_disjoint_iff.1 h
  have hxf' : (f : X ≃ₜ X) x ≠ x := hxf
  have hxk' : (k : X ≃ₜ X) x ≠ x := hxk
  obtain ⟨W, hWc, hxW, hWf, hWk⟩ := h01 X (f : X ≃ₜ X) (k : X ≃ₜ X) x hxf' hxk'
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hne⟩ := h05 X T hT W hWc.isOpen ⟨x, hxW⟩
  have kab : ⁅⁅(a : X ≃ₜ X), (f : X ≃ₜ X)⁆, (b : X ≃ₜ X)⁆ = ⁅(a : X ≃ₜ X), (b : X ≃ₜ X)⁆ :=
    h02 X (a : X ≃ₜ X) (b : X ≃ₜ X) (f : X ≃ₜ X) W ha hb hWf
  have kcd : ⁅⁅(c : X ≃ₜ X), (k : X ≃ₜ X)⁆, (d : X ≃ₜ X)⁆ = ⁅(c : X ≃ₜ X), (d : X ≃ₜ X)⁆ :=
    h02 X (c : X ≃ₜ X) (d : X ≃ₜ X) (k : X ≃ₜ X) W hc hd hWk
  have e1 : ⁅⁅a, f⁆, b⁆ = ⁅a, b⁆ :=
    Subtype.ext (by
      simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using kab)
  have e2 : ⁅⁅c, k⁆, d⁆ = ⁅c, d⁆ :=
    Subtype.ext (by
      simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using kcd)
  refine ⟨a, b, c, d, fun h1 => hne ?_⟩
  rwa [e1, e2] at h1

/-- Contrapositive form: if every double commutator `⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆` vanishes, the
moved sets of `f` and `k` are disjoint. -/
theorem disjoint_movedSet_of_forall_commutator_eq_one_of_statements
    (h01 : NonDisjWitDisplacedStatement) (h02 : NonDisjWitCommLocalStatement)
    (h05 : NonDisjWitNonMetabelianStatement) {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {f k : topologicalFullGroup T}
    (hall : ∀ a b c d : topologicalFullGroup T, ⁅⁅⁅a, f⁆, b⁆, ⁅⁅c, k⁆, d⁆⁆ = 1) :
    Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) := by
  by_contra h
  obtain ⟨a, b, c, d, hne⟩ :=
    exists_commutator_witness_of_not_disjoint_of_statements h01 h02 h05 hT h
  exact hne (hall a b c d)

/-- The universal `Statement` form of lane `sk-flip-07`, from the interfaces of lanes 01, 02
and 05. -/
theorem commutatorWitnessOfNotDisjoint_of_statements (h01 : NonDisjWitDisplacedStatement)
    (h02 : NonDisjWitCommLocalStatement) (h05 : NonDisjWitNonMetabelianStatement) :
    CommutatorWitnessOfNotDisjointStatement :=
  fun _ _ _ _ _ _ _ _ hT _ _ h =>
    exists_commutator_witness_of_not_disjoint_of_statements h01 h02 h05 hT h

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.CommutatorWitnessOfNotDisjointStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_commutator_witness_of_not_disjoint_of_statements
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.disjoint_movedSet_of_forall_commutator_eq_one_of_statements
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.commutatorWitnessOfNotDisjoint_of_statements
