import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingChains
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PendantRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExterior
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4, (38): counting the cutting sides

Osin (math/0411039v3, §9), proof of Lemma 9.4, (38): "`k_i ≤ 4 n_i`".  This module proves the
cutting half, `OsinLemma94CuttingSidesStatement`, from the forest property
`SameFaceDartForestStatement`.

Let `F` be the darts with the face `f` of polygon `k` on both sides.  These are exactly the darts
of the cutting sides.

* A *start* is a dart of `F` whose predecessor at its vertex is not in `F`.  Its predecessor on
  the walk is then off `F`, so a start is the first dart of an entry, or of side `0`
  (`card_sameFaceStarts_le`).
* A *turn* is a dart of `F` whose predecessor at its vertex is in `F` and differs from its
  successor there.  Two consecutive cutting sides `j`, `j + 1` meet at a turn, by `Maximal`.
* At one vertex, the turns plus six are at most three times the darts of `F` plus three times the
  starts (`card_filter_turns_add_six_le`).  Here a dart-minimal family has no vertex of valence
  one on `F`.  Summed over the vertices, with the forest property, the turns plus six are at most
  three times the starts (`card_sameFaceTurns_add_six_le`).

So the cutting sides are at most the entries, plus the turns, plus one:
`4 e + 1`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.4 inside
the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace CombMap

variable (M : CombMap.{u})

open Classical in
/-- The darts with the face `f` on both sides whose predecessor at their vertex has not. -/
noncomputable def sameFaceStarts (f : M.Face) : Finset M.Dart :=
  (M.sameFaceDarts f).filter fun y => M.sigma.symm y ∉ M.sameFaceDarts f

open Classical in
/-- The darts with the face `f` on both sides whose predecessor at their vertex also has it, and
whose successor at their vertex is not that predecessor. -/
noncomputable def sameFaceTurns (f : M.Face) : Finset M.Dart :=
  (M.sameFaceDarts f).filter fun y =>
    M.sigma.symm y ∈ M.sameFaceDarts f ∧ M.sigma y ≠ M.sigma.symm y

open Classical in
theorem mem_sameFaceStarts {f : M.Face} {y : M.Dart} :
    y ∈ M.sameFaceStarts f ↔ y ∈ M.sameFaceDarts f ∧ M.sigma.symm y ∉ M.sameFaceDarts f := by
  unfold sameFaceStarts
  rw [Finset.mem_filter]

open Classical in
theorem mem_sameFaceTurns {f : M.Face} {y : M.Dart} :
    y ∈ M.sameFaceTurns f ↔ y ∈ M.sameFaceDarts f ∧
      (M.sigma.symm y ∈ M.sameFaceDarts f ∧ M.sigma y ≠ M.sigma.symm y) := by
  unfold sameFaceTurns
  rw [Finset.mem_filter]

/-- The face `f` on both sides is kept under edge reversal. -/
theorem alpha_mem_sameFaceDarts {f : M.Face} {d : M.Dart} (hd : d ∈ M.sameFaceDarts f) :
    M.alpha d ∈ M.sameFaceDarts f := by
  rw [M.mem_sameFaceDarts] at hd ⊢
  exact ⟨hd.2, by rw [M.alpha_involutive d]; exact hd.1⟩

theorem vertexOf_sigma_symm (y : M.Dart) : M.vertexOf (M.sigma.symm y) = M.vertexOf y := by
  have h := M.vertexOf_sigma (M.sigma.symm y)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

open Classical in
/-- **At one vertex.**  If no dart of `F` is fixed by the vertex rotation, then at a vertex of
`F` the turns plus six are at most three times the darts of `F` plus three times the starts.
With a start, the turns and the starts are disjoint darts of `F`.  Without a start, the vertex
has at least two darts of `F`, and with exactly two the rotation swaps them, so there is no
turn. -/
theorem card_filter_turns_add_six_le {f : M.Face}
    (hfix : ∀ x ∈ M.sameFaceDarts f, M.sigma x ≠ x) {v : M.Vertex}
    (hv : v ∈ M.sameFaceVertices f) :
    ((M.sameFaceTurns f).filter fun y => M.vertexOf y = v).card + 6 ≤
      3 * ((M.sameFaceDarts f).filter fun y => M.vertexOf y = v).card +
        3 * ((M.sameFaceStarts f).filter fun y => M.vertexOf y = v).card := by
  have hv' : v ∈ (M.sameFaceDarts f).image M.vertexOf := hv
  obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hv'
  have hsub3 : ((M.sameFaceTurns f).filter fun y => M.vertexOf y = M.vertexOf x) ⊆
      (M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨(M.mem_sameFaceTurns.mp hy.1).1, hy.2⟩
  have hsub1 : ((M.sameFaceStarts f).filter fun y => M.vertexOf y = M.vertexOf x) ⊆
      (M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨(M.mem_sameFaceStarts.mp hy.1).1, hy.2⟩
  have hdisj : Disjoint ((M.sameFaceTurns f).filter fun y => M.vertexOf y = M.vertexOf x)
      ((M.sameFaceStarts f).filter fun y => M.vertexOf y = M.vertexOf x) := by
    rw [Finset.disjoint_left]
    intro y hy3 hy1
    exact (M.mem_sameFaceStarts.mp (Finset.mem_filter.mp hy1).1).2
      (M.mem_sameFaceTurns.mp (Finset.mem_filter.mp hy3).1).2.1
  have hunion := Finset.card_le_card (Finset.union_subset hsub3 hsub1)
  rw [Finset.card_union_of_disjoint hdisj] at hunion
  have hxv : x ∈ (M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x :=
    Finset.mem_filter.mpr ⟨hxF, rfl⟩
  have hpos := Finset.card_pos.mpr ⟨x, hxv⟩
  rcases Finset.eq_empty_or_nonempty
      ((M.sameFaceStarts f).filter fun y => M.vertexOf y = M.vertexOf x) with h1 | h1
  · rw [h1, Finset.card_empty] at hunion ⊢
    have hpred : ∀ y ∈ M.sameFaceDarts f, M.vertexOf y = M.vertexOf x →
        M.sigma.symm y ∈ M.sameFaceDarts f := by
      intro y hy hyv
      by_contra hn
      have hy1 : y ∈ (M.sameFaceStarts f).filter fun y => M.vertexOf y = M.vertexOf x :=
        Finset.mem_filter.mpr ⟨M.mem_sameFaceStarts.mpr ⟨hy, hn⟩, hyv⟩
      rw [h1] at hy1
      exact Finset.notMem_empty _ hy1
    have hne : ∀ y ∈ M.sameFaceDarts f, M.sigma.symm y ≠ y := by
      intro y hy h
      apply hfix y hy
      calc M.sigma y = M.sigma (M.sigma.symm y) := by rw [h]
        _ = y := Equiv.apply_symm_apply _ _
    have hmem : ∀ y ∈ (M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x,
        M.sigma.symm y ∈ (M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x := by
      intro y hy
      obtain ⟨hyF, hyv⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hpred y hyF hyv, (M.vertexOf_sigma_symm y).trans hyv⟩
    have htwo : 1 < ((M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x).card :=
      Finset.one_lt_card.mpr ⟨x, hxv, M.sigma.symm x, hmem x hxv, (hne x hxF).symm⟩
    by_cases h3 : 3 ≤ ((M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x).card
    · have := Finset.card_le_card hsub3
      omega
    · have hcard : ((M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x).card = 2 := by
        omega
      obtain ⟨a, b, _hab, hFv⟩ := Finset.card_eq_two.mp hcard
      have ha : a ∈ (M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x := by
        rw [hFv]
        exact Finset.mem_insert_self a {b}
      have hb : b ∈ (M.sameFaceDarts f).filter fun y => M.vertexOf y = M.vertexOf x := by
        rw [hFv]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      have hsa : M.sigma.symm a = b := by
        have h := hmem a ha
        rw [hFv, Finset.mem_insert, Finset.mem_singleton] at h
        exact h.resolve_left (hne a (Finset.mem_filter.mp ha).1)
      have hsb : M.sigma.symm b = a := by
        have h := hmem b hb
        rw [hFv, Finset.mem_insert, Finset.mem_singleton] at h
        exact h.resolve_right (hne b (Finset.mem_filter.mp hb).1)
      have hturn : ((M.sameFaceTurns f).filter fun y => M.vertexOf y = M.vertexOf x) ⊆ ∅ := by
        intro y hy
        exfalso
        have hyFv := hsub3 hy
        have hyT := (M.mem_sameFaceTurns.mp (Finset.mem_filter.mp hy).1).2.2
        rw [hFv, Finset.mem_insert, Finset.mem_singleton] at hyFv
        rcases hyFv with hya | hyb
        · rw [hya] at hyT
          apply hyT
          rw [hsa, ← hsb, Equiv.apply_symm_apply]
        · rw [hyb] at hyT
          apply hyT
          rw [hsb, ← hsa, Equiv.apply_symm_apply]
      have h0 := Finset.card_le_card hturn
      rw [Finset.card_empty] at h0
      omega
  · have := Finset.card_pos.mpr h1
    omega

open Classical in
/-- **Turns against starts.**  Summed over the vertices, with the forest property, the turns
plus six are at most three times the starts. -/
theorem card_sameFaceTurns_add_six_le (hforest : SameFaceDartForestStatement.{u})
    (hM : M.IsPlanar) {f : M.Face} (hne : (M.sameFaceDarts f).Nonempty)
    (hfix : ∀ x ∈ M.sameFaceDarts f, M.sigma x ≠ x) :
    (M.sameFaceTurns f).card + 6 ≤ 3 * (M.sameFaceStarts f).card := by
  have hmaps : ∀ s ⊆ M.sameFaceDarts f,
      Set.MapsTo M.vertexOf (s : Set M.Dart) (M.sameFaceVertices f) := by
    intro s hs x hx
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem M.vertexOf (hs (Finset.mem_coe.mp hx)))
  have hT : (M.sameFaceTurns f).card = ∑ v ∈ M.sameFaceVertices f,
      ((M.sameFaceTurns f).filter fun y => M.vertexOf y = v).card :=
    Finset.card_eq_sum_card_fiberwise (hmaps _ fun y hy => (M.mem_sameFaceTurns.mp hy).1)
  have hF : (M.sameFaceDarts f).card = ∑ v ∈ M.sameFaceVertices f,
      ((M.sameFaceDarts f).filter fun y => M.vertexOf y = v).card :=
    Finset.card_eq_sum_card_fiberwise (hmaps _ (Finset.Subset.refl _))
  have hS : (M.sameFaceStarts f).card = ∑ v ∈ M.sameFaceVertices f,
      ((M.sameFaceStarts f).filter fun y => M.vertexOf y = v).card :=
    Finset.card_eq_sum_card_fiberwise (hmaps _ fun y hy => (M.mem_sameFaceStarts.mp hy).1)
  have hsum := Finset.sum_le_sum fun v (hv : v ∈ M.sameFaceVertices f) =>
    M.card_filter_turns_add_six_le hfix hv
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    ← Finset.mul_sum, ← Finset.mul_sum, ← hT, ← hF, ← hS] at hsum
  have hforest' := hforest M hM f hne
  omega

end CombMap

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- Splitting `(range n).flatMap B` at block `i`. -/
theorem range_flatMap_eq_split {α : Type*} (B : ℕ → List α) {n i : ℕ} (hi : i < n) :
    (List.range n).flatMap B = (List.range i).flatMap B ++ B i ++
      ((List.range (n - (i + 1))).map ((i + 1) + ·)).flatMap B := by
  obtain ⟨m, rfl⟩ : ∃ m, n = i + 1 + m := ⟨n - (i + 1), by omega⟩
  rw [List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_sub_cancel_left]

/-- The walk of polygon `k`, read side by side, follows the face permutation. -/
theorem walk_isChain (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    ((List.range (P.sideCount k)).flatMap (P.sideDarts k)).IsChain
      fun d e => S.diagram.toCombMap.facePerm d = e := by
  rw [← P.walk k]
  exact Embedded.isChain_rotate_of_isChain_closes (S.diagram.faceBoundary (P.face k)).nonempty
    (S.diagram.faceBoundary (P.face k)).chain (S.diagram.faceBoundary (P.face k)).closes
    (P.base k)

/-- A dart of a side that is not its first dart follows another dart of the side. -/
theorem exists_facePerm_eq_of_not_head (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    {i : ℕ} (hi : i < P.sideCount k) {y : S.diagram.toCombMap.Dart}
    (hy : y ∈ P.sideDarts k i) (hhead : y ∉ (P.sideDarts k i).head?) :
    ∃ x ∈ P.sideDarts k i, S.diagram.toCombMap.facePerm x = y := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hy
  have hs : s ≠ [] := by
    rintro rfl
    apply hhead
    rw [hst]
    exact rfl
  have hinf : P.sideDarts k i <:+: (List.range (P.sideCount k)).flatMap (P.sideDarts k) := by
    rw [range_flatMap_eq_split (P.sideDarts k) hi]
    exact ⟨_, _, rfl⟩
  have hchain := (P.walk_isChain k).infix hinf
  rw [hst] at hchain
  refine ⟨s.getLast hs, ?_, ?_⟩
  · rw [hst]
    exact List.mem_append_left _ (List.getLast_mem hs)
  · exact (List.isChain_append.mp hchain).2.2 _ (List.getLast?_eq_some_getLast hs) _ rfl

/-- The last dart of a side and the first dart of the next side follow the face permutation. -/
theorem facePerm_getLast_eq_head (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {j : ℕ}
    (hj : j + 1 < P.sideCount k) {e e' : S.diagram.toCombMap.Dart}
    (he : e ∈ (P.sideDarts k j).getLast?) (he' : e' ∈ (P.sideDarts k (j + 1)).head?) :
    S.diagram.toCombMap.facePerm e = e' := by
  have hinf : P.sideDarts k j ++ P.sideDarts k (j + 1) <:+:
      (List.range (P.sideCount k)).flatMap (P.sideDarts k) := by
    rw [range_flatMap_eq_split (P.sideDarts k) hj, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc ((List.range j).flatMap (P.sideDarts k))]
    exact ⟨_, _, rfl⟩
  exact (List.isChain_append.mp ((P.walk_isChain k).infix hinf)).2.2 e he e' he'

open Classical in
/-- The cutting sides whose cyclic predecessor is also a cutting side. -/
noncomputable def continuationSides (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Finset ℕ :=
  (P.cuttingSides k).filter fun i =>
    P.kind k ((i + P.sideCount k - 1) % P.sideCount k) = .cutting

open Classical in
theorem mem_continuationSides (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ) :
    i ∈ P.continuationSides k ↔ (i < P.sideCount k ∧ P.kind k i = .cutting) ∧
      P.kind k ((i + P.sideCount k - 1) % P.sideCount k) = .cutting := by
  unfold continuationSides
  rw [Finset.mem_filter, mem_cuttingSides]

open Classical in
/-- **(38), the cutting half, over the forest property.** -/
theorem card_cuttingSides_le (hforest : SameFaceDartForestStatement.{v}) (hS : S.DartMinimal)
    (P : OsinLemma94RealizedPolygons S) (hmax : P.Maximal) (k : Fin P.count) :
    (P.cuttingSides k).card ≤ 4 * (P.cuttingEntries k).card + 1 := by
  have hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ≠ P.face k := by
    intro cell hcell
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hcell
    exact P.face_not_cell k j
  have hf : S.UnselectedGFace (P.face k) := ⟨P.face_ne_outer k, hcells, P.face_unselected k⟩
  have hfix : ∀ x ∈ S.diagram.toCombMap.sameFaceDarts (P.face k),
      S.diagram.toCombMap.sigma x ≠ x := by
    intro x hx h
    obtain ⟨-, hx2⟩ := (S.diagram.toCombMap.mem_sameFaceDarts _ x).mp hx
    refine GloballyDistinguishedSectionFamily.not_leaf_of_dartMinimal
      GloballyDistinguishedSectionFamily.pendantPathRemovalInput hS hf hx2 ?_
    show S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha x)) =
      S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha x)
    rw [S.diagram.toCombMap.alpha_involutive x]
    exact h
  have hW2 : ∀ i, i < P.sideCount k → P.kind k i = .cutting → ∀ d ∈ P.sideDarts k i,
      d ∈ S.diagram.toCombMap.sameFaceDarts (P.face k) := by
    intro i hi hkind d hd
    exact (S.diagram.toCombMap.mem_sameFaceDarts _ d).mpr
      ⟨P.faceOf_of_mem_sideDarts hi hd, P.cutting_internal k i hi hkind d hd⟩
  have hW3 : ∀ i, i < P.sideCount k → P.kind k i ≠ .cutting → ∀ d ∈ P.sideDarts k i,
      d ∉ S.diagram.toCombMap.sameFaceDarts (P.face k) := by
    intro i hi hkind d hd hdF
    have halpha := ((S.diagram.toCombMap.mem_sameFaceDarts _ d).mp hdF).2
    cases hk : P.kind k i with
    | cell j =>
      obtain ⟨arc, harc⟩ := P.cell_arc k i j hi hk
      rw [harc] at hd
      simp only [Embedded.CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hd
      obtain ⟨e, he, rfl⟩ := hd
      rw [S.diagram.toCombMap.alpha_involutive e] at halpha
      exact P.face_not_cell k j
        ((Embedded.faceOf_of_mem_cellDarts (arc.mem_cycle_of_mem_darts he)).symm.trans halpha)
    | boundary j =>
      obtain ⟨_hj, arc, harc, _, _⟩ := P.boundary_arc k i j hi hk
      rw [harc] at hd
      exact P.face_ne_outer k (halpha.symm.trans
        (Embedded.faceOf_alpha_of_mem_targetArc_none S.diagram none arc rfl hd))
    | cutting => exact hkind hk
    | short =>
      obtain ⟨a, ha, hall⟩ := P.short_region k i hi hk
      have h := hall d hd
      rw [halpha] at h
      exact P.face_unselected k a ha h
  have hW7 : ∀ y, S.diagram.toCombMap.faceOf y = P.face k →
      ∃ i, i < P.sideCount k ∧ y ∈ P.sideDarts k i := by
    intro y hy
    have hmem : y ∈ (S.diagram.faceBoundary (P.face k)).darts :=
      ((S.diagram.faceBoundary (P.face k)).mem_iff y).mpr hy
    have hwalk : y ∈ (List.range (P.sideCount k)).flatMap (P.sideDarts k) := by
      rw [← P.walk k]
      exact List.mem_rotate.mpr hmem
    obtain ⟨i, hi, hyi⟩ := List.mem_flatMap.mp hwalk
    exact ⟨i, List.mem_range.mp hi, hyi⟩
  have hheadInj : ∀ i, i < P.sideCount k → ∀ j, j < P.sideCount k →
      ∀ y, y ∈ (P.sideDarts k i).head? → y ∈ (P.sideDarts k j).head? → i = j := by
    intro i hi j hj y hyi hyj
    by_contra hij
    exact P.sideDarts_disjoint k hi hj hij (List.mem_of_mem_head? hyi)
      (List.mem_of_mem_head? hyj)
  have hhead : ∀ i, i < P.sideCount k → ∀ x0,
      (P.sideDarts k i).headD x0 ∈ (P.sideDarts k i).head? := by
    intro i hi x0
    obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (P.side_ne_nil k i hi)
    rw [hal]
    exact rfl
  rcases (P.cuttingSides k).eq_empty_or_nonempty with hC | ⟨i0, hi0⟩
  · rw [hC, Finset.card_empty]
    omega
  obtain ⟨hi0n, hi0k⟩ := (P.mem_cuttingSides k i0).mp hi0
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ (P.side_ne_nil k i0 hi0n)
  have hx0F := hW2 i0 hi0n hi0k x0 hx0
  -- cutting sides: entries and continuations
  have hsubET : P.cuttingSides k ⊆ P.cuttingEntries k ∪ P.continuationSides k := by
    intro i hi
    by_cases hp : P.kind k ((i + P.sideCount k - 1) % P.sideCount k) = .cutting
    · exact Finset.mem_union_right _
        ((P.mem_continuationSides k i).mpr ⟨(P.mem_cuttingSides k i).mp hi, hp⟩)
    · exact Finset.mem_union_left _
        ((P.mem_cuttingEntries k i).mpr ⟨(P.mem_cuttingSides k i).mp hi, hp⟩)
  have hCET := (Finset.card_le_card hsubET).trans (Finset.card_union_le _ _)
  have hT : (P.continuationSides k).card ≤ ((P.continuationSides k).erase 0).card + 1 := by
    have hsubT : P.continuationSides k ⊆ insert 0 ((P.continuationSides k).erase 0) := by
      intro i hi
      by_cases h0 : i = 0
      · rw [h0]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h0, hi⟩)
    exact (Finset.card_le_card hsubT).trans (Finset.card_insert_le _ _)
  -- continuations after side `0` start at turns
  have hTurns : ((P.continuationSides k).erase 0).card ≤
      (S.diagram.toCombMap.sameFaceTurns (P.face k)).card := by
    refine Finset.card_le_card_of_injOn (fun i => (P.sideDarts k i).headD x0) ?_ ?_
    · intro i hi
      obtain ⟨hi0, hiT⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hi)
      obtain ⟨⟨hin, hik⟩, hpred⟩ := (P.mem_continuationSides k i).mp hiT
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hjn : j < P.sideCount k := by omega
      have hpj : (j + 1 + P.sideCount k - 1) % P.sideCount k = j := by
        rw [show j + 1 + P.sideCount k - 1 = j + P.sideCount k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hjn]
      rw [hpj] at hpred
      obtain ⟨e, he⟩ : ∃ e, e ∈ (P.sideDarts k j).getLast? :=
        ⟨_, List.getLast?_eq_some_getLast (P.side_ne_nil k j hjn)⟩
      have hy := hhead (j + 1) hin x0
      have hperm := P.facePerm_getLast_eq_head hin he hy
      have heF := hW2 j hjn hpred e (List.mem_of_mem_getLast? he)
      have hyF := hW2 (j + 1) hin hik _ (List.mem_of_mem_head? hy)
      have hsymm : S.diagram.toCombMap.sigma.symm ((P.sideDarts k (j + 1)).headD x0) =
          S.diagram.toCombMap.alpha e := by
        rw [Equiv.symm_apply_eq]
        exact hperm.symm
      have hmx := (hmax k j hin (hpred.trans hik.symm) e he _ hy).1
        (by rw [hpred]; intro h; cases h)
      refine Finset.mem_coe.mpr ?_
      show (P.sideDarts k (j + 1)).headD x0 ∈ S.diagram.toCombMap.sameFaceTurns (P.face k)
      refine S.diagram.toCombMap.mem_sameFaceTurns.mpr ⟨hyF, ?_, ?_⟩
      · rw [hsymm]
        exact S.diagram.toCombMap.alpha_mem_sameFaceDarts heF
      · rw [hsymm]
        intro h
        apply hmx
        show S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha
          (S.diagram.toCombMap.alpha ((P.sideDarts k (j + 1)).headD x0))) =
            S.diagram.toCombMap.alpha e
        rw [S.diagram.toCombMap.alpha_involutive ((P.sideDarts k (j + 1)).headD x0)]
        exact h
    · intro i hi i' hi' hii'
      have hin := ((P.mem_continuationSides k i).mp
        (Finset.mem_erase.mp (Finset.mem_coe.mp hi)).2).1.1
      have hin' := ((P.mem_continuationSides k i').mp
        (Finset.mem_erase.mp (Finset.mem_coe.mp hi')).2).1.1
      have heq : (P.sideDarts k i).headD x0 = (P.sideDarts k i').headD x0 := hii'
      have hy := hhead i hin x0
      have hy' := hhead i' hin' x0
      rw [heq] at hy
      exact hheadInj i hin i' hin' _ hy hy'
  -- starts are first darts of entries, or of side `0`
  have hStarts : (S.diagram.toCombMap.sameFaceStarts (P.face k)).card ≤
      (P.cuttingEntries k).card + 1 := by
    have hsub : S.diagram.toCombMap.sameFaceStarts (P.face k) ⊆
        insert ((P.sideDarts k 0).headD x0)
          ((P.cuttingEntries k).image fun i => (P.sideDarts k i).headD x0) := by
      intro y hy
      obtain ⟨hyF, hys⟩ := S.diagram.toCombMap.mem_sameFaceStarts.mp hy
      obtain ⟨i, hi, hyi⟩ := hW7 y ((S.diagram.toCombMap.mem_sameFaceDarts _ y).mp hyF).1
      have hik : P.kind k i = .cutting := by
        by_contra hne
        exact hW3 i hi hne y hyi hyF
      by_cases hyh : y ∈ (P.sideDarts k i).head?
      · have hyeq : y = (P.sideDarts k i).headD x0 := by
          have h := hhead i hi x0
          rw [Option.mem_def] at h hyh
          exact Option.some.inj (hyh.symm.trans h)
        rcases Nat.eq_zero_or_pos i with h0 | _hpos
        · rw [hyeq, h0]
          exact Finset.mem_insert_self _ _
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          have hjn : j < P.sideCount k := by omega
          obtain ⟨e, he⟩ : ∃ e, e ∈ (P.sideDarts k j).getLast? :=
            ⟨_, List.getLast?_eq_some_getLast (P.side_ne_nil k j hjn)⟩
          have hperm := P.facePerm_getLast_eq_head hi he hyh
          have hsymm : S.diagram.toCombMap.sigma.symm y = S.diagram.toCombMap.alpha e := by
            rw [Equiv.symm_apply_eq]
            exact hperm.symm
          have hjk : P.kind k j ≠ .cutting := by
            intro hjc
            apply hys
            rw [hsymm]
            exact S.diagram.toCombMap.alpha_mem_sameFaceDarts
              (hW2 j hjn hjc e (List.mem_of_mem_getLast? he))
          have hpj : (j + 1 + P.sideCount k - 1) % P.sideCount k = j := by
            rw [show j + 1 + P.sideCount k - 1 = j + P.sideCount k by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt hjn]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j + 1, ?_, hyeq.symm⟩)
          exact (P.mem_cuttingEntries k (j + 1)).mpr ⟨⟨hi, hik⟩, by rw [hpj]; exact hjk⟩
      · exfalso
        obtain ⟨x, hx, hxy⟩ := P.exists_facePerm_eq_of_not_head hi hyi hyh
        apply hys
        have hsymm : S.diagram.toCombMap.sigma.symm y = S.diagram.toCombMap.alpha x := by
          rw [Equiv.symm_apply_eq]
          exact hxy.symm
        rw [hsymm]
        exact S.diagram.toCombMap.alpha_mem_sameFaceDarts (hW2 i hi hik x hx)
    have himage := Finset.card_image_le (s := P.cuttingEntries k)
      (f := fun i => (P.sideDarts k i).headD x0)
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))
  have hglob := S.diagram.toCombMap.card_sameFaceTurns_add_six_le hforest S.diagram.planar
    ⟨x0, hx0F⟩ hfix
  omega

end OsinLemma94RealizedPolygons

/-- **(38), the cutting half, from the forest property.**  Osin, proof of Lemma 9.4, (38):
"`k_i ≤ 4 n_i`", for the cutting sides. -/
theorem osinLemma94CuttingSides_of_forest (hforest : SameFaceDartForestStatement.{v}) :
    OsinLemma94CuttingSidesStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S hS P hmax k
  exact P.card_cuttingSides_le hforest hS hmax k

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.card_filter_turns_add_six_le
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.card_sameFaceTurns_add_six_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_cuttingSides_le
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CuttingSides_of_forest
