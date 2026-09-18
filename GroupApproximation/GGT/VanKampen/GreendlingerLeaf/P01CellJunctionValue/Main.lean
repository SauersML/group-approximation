import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Bridge
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Pocket
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Hole
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassProducerGaps
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassTransitions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionExclusion
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell junction gaps read `1`: the case split

At a kind-level same-cell join of side `s` the corner gives `a = α e'`, `b = α e`, and `m` least
with `facePerm^(m + 1) a = b`.  If `m = 0` the gap is empty.  Otherwise pick an outer dart `o`;
after the corner is split, `o` is reached from `b` or from `facePerm a`
(`JunctionPocket.reach_or_reach`).

* From `b` (Case A): `listVal_gap_eq_one`.
* From `facePerm a` (Case B): the polygon face lies in a hole region of the cell
  (`exists_holeRegion`), so every side is an arc of the cell (`kind_eq_cell`) and every side joins
  the next at kind level.
  For every other side `t`, of the two junctions `s`, `t` the outer dart is on the face side of one
  (`JunctionPocket.reach_face_or_reach_face`); not of `s`, so of `t`, and side `t` is a class join
  by Case A.  So at most one side is a class non-join, against the hypothesis.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The corner of a same-cell join.** -/
theorem corner_data (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    (hs : s < P.sideCount k) {j : Fin S.diagram.rCellCount} (hj : P.kind k s = .cell j)
    (hjoin : P.KindJoins k s) :
    ∃ e e' : S.diagram.toCombMap.Dart, (P.sideDarts k s).getLast? = some e ∧
      (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some e' ∧ e ∈ P.sideDarts k s ∧
      S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha e) =
        S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e') ∧
      S.diagram.toCombMap.alpha e' ∈ cellDarts S.diagram j ∧
      S.diagram.toCombMap.faceOf e = P.face k ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e)) ≠
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e') ∧
      ∃ m, (S.diagram.toCombMap.facePerm ^ (m + 1)) (S.diagram.toCombMap.alpha e') =
        S.diagram.toCombMap.alpha e := by
  have hpos : 0 < P.sideCount k := by omega
  have hs' : (s + 1) % P.sideCount k < P.sideCount k := Nat.mod_lt _ hpos
  obtain ⟨e, he⟩ : ∃ e, (P.sideDarts k s).getLast? = some e :=
    Option.ne_none_iff_exists'.mp fun h => P.side_ne_nil k s hs (List.getLast?_eq_none_iff.mp h)
  obtain ⟨e', he'⟩ : ∃ e', (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some e' :=
    Option.ne_none_iff_exists'.mp fun h => P.side_ne_nil k _ hs' (List.head?_eq_none_iff.mp h)
  have hj' : P.kind k ((s + 1) % P.sideCount k) = .cell j := by
    rw [← hjoin.1, hj]
  have hemem : e ∈ P.sideDarts k s := List.mem_of_mem_getLast? (Option.mem_def.mpr he)
  have hemem' : e' ∈ P.sideDarts k ((s + 1) % P.sideCount k) :=
    List.mem_of_mem_head? (Option.mem_def.mpr he')
  have hb : S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha e) =
      S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e') := by
    rw [S.diagram.toCombMap.alpha_involutive e']
    exact P.facePerm_getLast_eq_head_mod hs (Option.mem_def.mpr he) (Option.mem_def.mpr he')
  have hbcell := P.alpha_mem_cellDarts_of_mem_cellSideDarts hs hj hemem
  have hacell := P.alpha_mem_cellDarts_of_mem_cellSideDarts hs' hj' hemem'
  have hsame : S.diagram.toCombMap.facePerm.SameCycle
      (S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e'))
      (S.diagram.toCombMap.alpha e) := by
    rw [Equiv.Perm.sameCycle_apply_left, ← S.diagram.toCombMap.faceOf_eq_iff,
      ((S.diagram.faceBoundary (cell S.diagram j).face).mem_iff _).mp hacell,
      ((S.diagram.faceBoundary (cell S.diagram j).face).mem_iff _).mp hbcell]
  obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
  have hef : S.diagram.toCombMap.faceOf e = P.face k := P.faceOf_of_mem_sideDarts hs hemem
  have hface :
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e)) ≠
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e') := by
    rw [S.diagram.toCombMap.alpha_involutive e, hef,
      ((S.diagram.faceBoundary (cell S.diagram j).face).mem_iff _).mp hacell]
    exact fun h => P.face_not_cell k j h.symm
  exact ⟨e, e', he, he', hemem, hb, hacell, hef, hface, n,
    by rw [pow_succ, Equiv.Perm.mul_apply]; exact hn⟩

/-- **A same-cell gap reads `1` when the outer dart is on the face side** (or the gap is empty). -/
theorem listVal_junctionGap_of_reach (hNo : NoCellInside S.diagram)
    (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ} {j : Fin S.diagram.rCellCount}
    (hj : P.kind k s = .cell j) {e e' o : S.diagram.toCombMap.Dart}
    (he : (P.sideDarts k s).getLast? = some e)
    (he' : (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some e')
    (hb : S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha e) =
      S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e'))
    (hacell : S.diagram.toCombMap.alpha e' ∈ cellDarts S.diagram j)
    (hface : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e)) ≠
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e'))
    (hex : ∃ m, (S.diagram.toCombMap.facePerm ^ (m + 1)) (S.diagram.toCombMap.alpha e') =
      S.diagram.toCombMap.alpha e)
    (ho : S.diagram.toCombMap.faceOf o = S.diagram.outerFace)
    (hJ : Nat.find hex ≠ 0 → Relation.EqvGen (FoldMap.joined S.diagram.toCombMap
      ((S.diagram.toCombMap.facePerm ^ Nat.find hex) (S.diagram.toCombMap.alpha e'))
      (S.diagram.toCombMap.alpha e')).Adjacent (S.diagram.toCombMap.alpha e) o) :
    RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) = 1 := by
  rw [P.junctionGap_cell he he' hj]
  by_cases hm : Nat.find hex = 0
  · rw [ClassProducer.cellGapOf_eq_nil hex hm]
    rfl
  · rw [ClassProducer.cellGapOf, dif_pos hex]
    exact listVal_gap_eq_one S.diagram hNo hm hb (Nat.find_spec hex)
      (fun t ht => Nat.find_min hex ht) hface j hacell ho (hJ hm)

/-- **Same-cell junction gaps read `1`** on polygons with at least two class non-joins. -/
theorem main (hNo : NoCellInside S.diagram)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hmin : S.DartMinimal) (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    (h2 : 2 ≤ ((Finset.range (P.sideCount k)).filter fun s => ¬ P.ClassJoins k s).card)
    {s : ℕ} (hs : s < P.sideCount k) (hjoin : P.KindJoins k s) {j : Fin S.diagram.rCellCount}
    (hj : P.kind k s = .cell j) :
    RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) = 1 := by
  obtain ⟨e, e', he, he', hemem, hb, hacell, hef, hface, hex⟩ := corner_data P hs hj hjoin
  obtain ⟨o, homem⟩ := List.exists_mem_of_ne_nil _
    (S.diagram.faceBoundary S.diagram.outerFace).nonempty
  have ho : S.diagram.toCombMap.faceOf o = S.diagram.outerFace :=
    ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff o).mp homem
  refine listVal_junctionGap_of_reach hNo P hj he he' hb hacell hface hex ho fun hm => ?_
  have hab := Nat.find_spec hex
  have hleast : ∀ t < Nat.find hex, (S.diagram.toCombMap.facePerm ^ (t + 1))
      (S.diagram.toCombMap.alpha e') ≠ S.diagram.toCombMap.alpha e :=
    fun t ht => Nat.find_min hex ht
  rcases JunctionPocket.reach_or_reach S.diagram.planar.1
      ((S.diagram.toCombMap.facePerm ^ Nat.find hex) (S.diagram.toCombMap.alpha e'))
      (S.diagram.toCombMap.alpha e') o with hreach | hgap
  · rwa [JunctionPocket.facePerm_last hab] at hreach
  exfalso
  obtain ⟨E, hE⟩ := exists_holeRegion S.diagram hNo hm hb hab hleast hface j hacell ho hgap
  rw [S.diagram.toCombMap.alpha_involutive e, hef] at hE
  have hpos : 0 < P.sideCount k := by omega
  have hkind : ∀ i, i < P.sideCount k → P.kind k i = .cell j :=
    fun i hi => kind_eq_cell hvalue hmin P hE hi
  have hall : ∀ t, t < P.sideCount k → t ≠ s → P.ClassJoins k t := by
    intro t ht hts
    have hjt : P.kind k t = .cell j := hkind t ht
    have hjoint : P.KindJoins k t :=
      ⟨by rw [hjt, hkind ((t + 1) % P.sideCount k) (Nat.mod_lt (t + 1) hpos)], Or.inl ⟨j, hjt⟩⟩
    obtain ⟨et, et', het, het', hetmem, hbt, hacellt, heft, hfacet, hext⟩ :=
      corner_data P ht hjt hjoint
    refine ⟨hjoint, ?_, fun _ _ => P.junctionGap_faceOf_ne_face ht hjt hjoint, fun _ hbd => ?_⟩
    · refine listVal_junctionGap_of_reach hNo P hjt het het' hbt hacellt hfacet hext ho
        fun hmt => ?_
      have hsame : S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e)) =
          S.diagram.toCombMap.faceOf
            (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha et)) := by
        rw [S.diagram.toCombMap.alpha_involutive e, S.diagram.toCombMap.alpha_involutive et, hef,
          heft]
      have hne : S.diagram.toCombMap.alpha e ≠ S.diagram.toCombMap.alpha et := by
        intro hbe
        have hee : e = et := S.diagram.toCombMap.alpha.injective hbe
        rw [← hee] at hetmem
        exact P.sideDarts_disjoint k hs ht (fun h => hts h.symm) hemem hetmem
      rcases JunctionPocket.reach_face_or_reach_face S.diagram.planar hm hmt hb hbt hab
          (Nat.find_spec hext) hleast (fun t' ht' => Nat.find_min hext ht') hface hfacet hsame
          hne o with h' | h'
      · exact (JunctionPocket.junction_not_reach S.diagram.planar hm hb hab hleast
          (Relation.EqvGen.trans _ _ _ h' (Relation.EqvGen.symm _ _ hgap))).elim
      · exact h'
    · rw [hjt] at hbd
      cases hbd
  have hsub : ((Finset.range (P.sideCount k)).filter fun s => ¬ P.ClassJoins k s) ⊆
      ({s} : Finset ℕ) := by
    intro t htmem
    rw [Finset.mem_filter, Finset.mem_range] at htmem
    rw [Finset.mem_singleton]
    by_contra hts
    exact htmem.2 (hall t htmem.1 hts)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hcard
  exact absurd (h2.trans hcard) (by norm_num)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.corner_data
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.listVal_junctionGap_of_reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.main
