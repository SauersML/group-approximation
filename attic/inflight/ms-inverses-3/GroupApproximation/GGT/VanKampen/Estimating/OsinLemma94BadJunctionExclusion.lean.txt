import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassProducerGaps
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94JunctionPocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingSidesCount
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: bad junctions of the class producer, the planar part

Osin (math/0411039v3, §9), proof of Lemma 9.4.  The class producer joins two consecutive sides of a
polygon when they join at kind level (`KindJoins`) and, in addition, the gap between them reads a
word of value one, a same-cell gap has no dart on the polygon face, and a same-section junction moves
forward along `∂Δ` (`ClassJoins`, `Estimating/OsinLemma94ClassProducerGaps`).  The kind-level joins
that are not class joins are the bad junctions (`badJunctions`).

This module proves the planar part of the exclusion.

* `facePerm_getLast_eq_head_mod`: the last dart of side `s` and the first dart of side
  `(s + 1) % k_i` follow the face permutation, including the wrap from the last side to side `0`
  (`facePerm_getLast_last_eq_head_zero`).
* `junctionGap_faceOf_ne_face`: after a side of kind `cell j` that joins the next side at kind level,
  no dart of the gap lies on the polygon face.  This is hull-component's `JunctionPocket.gap_alpha_faceOf_ne`
  at the corner of the polygon walk, on the planar optimal diagram.
* `listVal_junctionGap_ne_one_of_mem_badJunctions`: so a bad same-cell junction is exactly a gap
  whose word does not have value one.
* Closed endpoint: `osinLemma94JunctionFaceClause : OsinLemma94JunctionFaceClauseStatement`.
* `card_badJunctions_le_boundaryBad`, `sum_card_badJunctions_le_sum_boundaryBad`: when every
  kind-level same-cell join has a gap of value one, the bad junctions are the boundary bad junctions
  (`boundaryBadJunctions`).

Residual pieces, stated over the polygons with an (A1) side and at least two class non-joins (the
index set agreed with ms-binary for `OsinLemma94BadJunctionInput`) and model-tested by hand in
`notes/nm-swarm/reports/ms-inverses-3.md`:
* `OsinLemma94CellJunctionValueInput`: the gap of a kind-level same-cell join has value one.  A pocket
  with a relator cell is a loop cut (`false_of_pocketRegion_of_below`); a pocket of `G`-faces has value
  one given a face assembly; with the exterior on the gap side the polygon lies in a hole of the cell
  and has one class non-join, so it is not in the index set.
* `OsinLemma94BoundaryJunctionBudgetInput`: the boundary bad junctions number at most `K n`.  A backward
  junction sees a lobe of `∂Δ` through the base dart, and a value failure a lobe carrying a relator
  cell.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4 inside the
proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The last dart of the last side and the first dart of side `0` follow the face permutation. -/
theorem facePerm_getLast_last_eq_head_zero (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    (hpos : 0 < P.sideCount k) {e e' : S.diagram.toCombMap.Dart}
    (he : e ∈ (P.sideDarts k (P.sideCount k - 1)).getLast?)
    (he' : e' ∈ (P.sideDarts k 0).head?) :
    S.diagram.toCombMap.facePerm e = e' := by
  have hne : (S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k) ≠ [] :=
    List.rotate_eq_nil_iff.not.mpr (S.diagram.faceBoundary (P.face k)).nonempty
  have hclose := Embedded.isChain_rotate_closing
    (R := fun d e => S.diagram.toCombMap.facePerm d = e)
    (S.diagram.faceBoundary (P.face k)).nonempty (S.diagram.faceBoundary (P.face k)).chain
    (S.diagram.faceBoundary (P.face k)).closes (P.base k) hne
  have hsplit := range_flatMap_eq_split (P.sideDarts k)
    (show P.sideCount k - 1 < P.sideCount k by omega)
  have htail : P.sideCount k - (P.sideCount k - 1 + 1) = 0 := by omega
  rw [htail, List.range_zero, List.map_nil, List.flatMap_nil, List.append_nil] at hsplit
  have hL : (S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k) =
      (List.range (P.sideCount k - 1)).flatMap (P.sideDarts k) ++
        P.sideDarts k (P.sideCount k - 1) := by
    rw [P.walk k, hsplit]
  have hL0 : (S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k) =
      P.sideDarts k 0 ++ ((List.range (P.sideCount k - 1)).map Nat.succ).flatMap (P.sideDarts k) := by
    rw [P.walk k]
    obtain ⟨m, hm⟩ : ∃ m, P.sideCount k = m + 1 := ⟨P.sideCount k - 1, by omega⟩
    rw [hm, List.range_succ_eq_map, List.flatMap_cons, Nat.add_sub_cancel]
  have hlast : e ∈ ((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k)).getLast? := by
    rw [hL, List.getLast?_append_of_ne_nil _ (P.side_ne_nil k _ (by omega))]
    exact he
  have hhead : e' ∈ ((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k)).head? := by
    rw [hL0, List.head?_append_of_ne_nil _ (P.side_ne_nil k 0 hpos)]
    exact he'
  obtain ⟨h1, rfl⟩ := List.mem_getLast?_eq_getLast hlast
  rw [List.head?_eq_some_head hne] at hhead
  exact hclose.trans (Option.some_inj.mp (Option.mem_def.mp hhead))

/-- **Consecutive sides, read cyclically.**  The last dart of side `s` and the first dart of side
`(s + 1) % k_i` follow the face permutation. -/
theorem facePerm_getLast_eq_head_mod (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    (hs : s < P.sideCount k) {e e' : S.diagram.toCombMap.Dart}
    (he : e ∈ (P.sideDarts k s).getLast?)
    (he' : e' ∈ (P.sideDarts k ((s + 1) % P.sideCount k)).head?) :
    S.diagram.toCombMap.facePerm e = e' := by
  by_cases hlt : s + 1 < P.sideCount k
  · rw [Nat.mod_eq_of_lt hlt] at he'
    exact P.facePerm_getLast_eq_head hlt he he'
  · have hsc : s = P.sideCount k - 1 := by omega
    have hmod : (s + 1) % P.sideCount k = 0 := by
      rw [show s + 1 = P.sideCount k by omega, Nat.mod_self]
    rw [hmod] at he'
    rw [hsc] at he
    exact P.facePerm_getLast_last_eq_head_zero (by omega) he he'

/-- The reverse of a dart on a side of kind `cell j` is a dart of the `j`-th relator cell. -/
theorem alpha_mem_cellDarts_of_mem_sideDarts (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    {i : ℕ} (hi : i < P.sideCount k) {j : Fin S.diagram.rCellCount} (hj : P.kind k i = .cell j)
    {d : S.diagram.toCombMap.Dart} (hd : d ∈ P.sideDarts k i) :
    S.diagram.toCombMap.alpha d ∈ cellDarts S.diagram j := by
  obtain ⟨arc, harc⟩ := P.cell_arc k i j hi hj
  rw [harc] at hd
  have hd' : d ∈ arc.darts.reverse.map S.diagram.toCombMap.alpha := hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd'
  rw [S.diagram.toCombMap.alpha_involutive x]
  exact arc.mem_cycle_of_mem_darts (List.mem_reverse.mp hx)

/-- **(B) at polygon level: a same-cell gap misses the polygon face.**  After a side of kind
`cell j` that joins the next side at kind level, no dart of the gap lies on the polygon face. -/
theorem junctionGap_faceOf_ne_face (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    (hs : s < P.sideCount k) {j : Fin S.diagram.rCellCount} (hj : P.kind k s = .cell j)
    (hjoin : P.KindJoins k s) :
    ∀ d ∈ P.junctionGap k s, S.diagram.toCombMap.faceOf d ≠ P.face k := by
  have hpos : 0 < P.sideCount k := by omega
  have hs' : (s + 1) % P.sideCount k < P.sideCount k := Nat.mod_lt _ hpos
  obtain ⟨e, he⟩ : ∃ e, (P.sideDarts k s).getLast? = some e :=
    Option.ne_none_iff_exists'.mp fun h => P.side_ne_nil k s hs (List.getLast?_eq_none_iff.mp h)
  obtain ⟨e', he'⟩ : ∃ e', (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some e' :=
    Option.ne_none_iff_exists'.mp fun h => P.side_ne_nil k _ hs' (List.head?_eq_none_iff.mp h)
  rw [P.junctionGap_cell he he' hj]
  have hj' : P.kind k ((s + 1) % P.sideCount k) = .cell j := by
    rw [← hjoin.1, hj]
  have hemem : e ∈ P.sideDarts k s := List.mem_of_mem_getLast? (Option.mem_def.mpr he)
  have hemem' : e' ∈ P.sideDarts k ((s + 1) % P.sideCount k) :=
    List.mem_of_mem_head? (Option.mem_def.mpr he')
  have hb : S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha e) =
      S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e') := by
    rw [S.diagram.toCombMap.alpha_involutive e']
    exact P.facePerm_getLast_eq_head_mod hs (Option.mem_def.mpr he) (Option.mem_def.mpr he')
  have hbcell := P.alpha_mem_cellDarts_of_mem_sideDarts hs hj hemem
  have hacell := P.alpha_mem_cellDarts_of_mem_sideDarts hs' hj' hemem'
  have hsame : S.diagram.toCombMap.facePerm.SameCycle
      (S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e'))
      (S.diagram.toCombMap.alpha e) := by
    rw [Equiv.Perm.sameCycle_apply_left, ← S.diagram.toCombMap.faceOf_eq_iff,
      ((S.diagram.faceBoundary (cell S.diagram j).face).mem_iff _).mp hacell,
      ((S.diagram.faceBoundary (cell S.diagram j).face).mem_iff _).mp hbcell]
  obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
  have hex : ∃ m, (S.diagram.toCombMap.facePerm ^ (m + 1)) (S.diagram.toCombMap.alpha e') =
      S.diagram.toCombMap.alpha e :=
    ⟨n, by rw [pow_succ, Equiv.Perm.mul_apply]; exact hn⟩
  intro d hd
  rw [ClassProducer.cellGapOf, dif_pos hex] at hd
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hd)
  have ht' : t < Nat.find hex := List.mem_range.mp ht
  have hef : S.diagram.toCombMap.faceOf e = P.face k := P.faceOf_of_mem_sideDarts hs hemem
  have hface : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha e)) ≠
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e') := by
    rw [S.diagram.toCombMap.alpha_involutive e, hef,
      ((S.diagram.faceBoundary (cell S.diagram j).face).mem_iff _).mp hacell]
    exact fun h => P.face_not_cell k j h.symm
  have key := JunctionPocket.gap_alpha_faceOf_ne S.diagram.planar (by omega) hb
    (Nat.find_spec hex) (fun t ht => Nat.find_min hex ht) hface ht'
  rwa [S.diagram.toCombMap.alpha_involutive e, hef] at key

/-- **A bad same-cell junction is a value failure.**  If side `s` of kind `cell j` is a bad junction,
the word of its gap does not have value one. -/
theorem listVal_junctionGap_ne_one_of_mem_badJunctions (P : OsinLemma94RealizedPolygons S)
    {k : Fin P.count} {s : ℕ} (hs : s ∈ P.badJunctions k) {j : Fin S.diagram.rCellCount}
    (hj : P.kind k s = .cell j) :
    RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) ≠ 1 := by
  obtain ⟨hsr, hjoin, hnot⟩ := Finset.mem_filter.mp hs
  have hsc := Finset.mem_range.mp hsr
  intro hval
  apply hnot
  refine ⟨hjoin, hval, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · rw [hj] at hj'
    cases hj'
    exact P.junctionGap_faceOf_ne_face hsc hj hjoin
  · rw [hj] at hj'
    cases hj'

/-- The bad junctions after a side of kind `boundary j`. -/
noncomputable def boundaryBadJunctions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.badJunctions k).filter fun s => ∃ j, P.kind k s = .boundary j

/-- **With value one on same-cell gaps, the bad junctions are boundary bad junctions.** -/
theorem card_badJunctions_le_boundaryBad (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (hval : ∀ s < P.sideCount k, P.KindJoins k s → ∀ j, P.kind k s = .cell j →
      RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) = 1) :
    (P.badJunctions k).card ≤ (P.boundaryBadJunctions k).card := by
  apply Finset.card_le_card
  intro s hs
  refine Finset.mem_filter.mpr ⟨hs, ?_⟩
  obtain ⟨hsr, hjoin, -⟩ := Finset.mem_filter.mp hs
  rcases hjoin.2 with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact absurd (hval s (Finset.mem_range.mp hsr) hjoin j hj)
      (P.listVal_junctionGap_ne_one_of_mem_badJunctions hs hj)
  · exact ⟨j, hj⟩

/-- The same, summed over any set of polygons. -/
theorem sum_card_badJunctions_le_sum_boundaryBad (P : OsinLemma94RealizedPolygons S)
    (T : Finset (Fin P.count))
    (hval : ∀ k ∈ T, ∀ s < P.sideCount k, P.KindJoins k s → ∀ j, P.kind k s = .cell j →
      RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) = 1) :
    ∑ k ∈ T, (P.badJunctions k).card ≤ ∑ k ∈ T, (P.boundaryBadJunctions k).card :=
  Finset.sum_le_sum fun k hk => P.card_badJunctions_le_boundaryBad k (hval k hk)

end OsinLemma94RealizedPolygons

/-- **The cell face clause of `ClassJoins`, for every kind-level same-cell join.**  For realized
polygons of any globally distinguished family, after a side of kind `cell j` that joins the next side
at kind level, no dart of the gap lies on the polygon face. -/
def OsinLemma94JunctionFaceClauseStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ), s < P.sideCount k →
      P.KindJoins k s → ∀ j, P.kind k s = .cell j →
        ∀ d ∈ P.junctionGap k s, S.diagram.toCombMap.faceOf d ≠ P.face k

theorem osinLemma94JunctionFaceClause : OsinLemma94JunctionFaceClauseStatement.{u, w, v} :=
  fun P _ _ hs hjoin _ hj => P.junctionGap_faceOf_ne_face hs hj hjoin

/-- **Value one on same-cell junction gaps (residual).**  At the parameters of Lemma 9.4, for `ρ`
large, with clause (b) of Lemma 9.7 below the number of relator cells of `Δ`: on a polygon with an
(A1) side and at least two class non-joins, the gap of every kind-level same-cell join has value one. -/
def OsinLemma94CellJunctionValueInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ k ∈ P.relatorPolygons,
                      2 ≤ ((Finset.range (P.sideCount k)).filter fun s => ¬ P.ClassJoins k s).card →
                        ∀ s < P.sideCount k, P.KindJoins k s → ∀ j, P.kind k s = .cell j →
                          RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) = 1

/-- **The boundary bad junctions (residual).**  At the parameters of Lemma 9.4, for `ρ` large, with
clause (b) of Lemma 9.7 below the number of relator cells of `Δ`: summed over the polygons with an
(A1) side and at least two class non-joins, the boundary bad junctions number at most `K n`. -/
def OsinLemma94BoundaryJunctionBudgetInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∑ k ∈ P.relatorPolygons.filter (fun k =>
                        2 ≤ ((Finset.range (P.sideCount k)).filter
                          fun s => ¬ P.ClassJoins k s).card),
                      (P.boundaryBadJunctions k).card ≤ K * Delta.rCellCount

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94JunctionFaceClause
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.facePerm_getLast_eq_head_mod
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.junctionGap_faceOf_ne_face
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.listVal_junctionGap_ne_one_of_mem_badJunctions
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_badJunctions_le_sum_boundaryBad
