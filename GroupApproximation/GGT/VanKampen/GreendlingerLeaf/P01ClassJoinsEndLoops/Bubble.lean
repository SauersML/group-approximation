import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.ClassPocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellCount
import GroupApproximation.Meta.AxiomGuard

/-!
# End loops of the class producer: the end loops and the covering of unbound darts

The end loops at budget `L` (a bound on the pocket lengths) are
* at a class: the reverses of the `L` face predecessors of the reverse of its last dart;
* at a region: the reverses of the `L` face predecessors of the reverses of its side darts,
  and the reverses of the `L` face predecessors of the first darts of its two arcs.

So a class loop has at most `L` darts and a region loop at most `(2 ε + 2) L` darts.

Take an unbound dart `d` of cell `i` across an (A1) side of a single-class polygon.  The walk of
that class is a pocket through `d`; take a longest pocket `seg x J` through `d`, `d = f^s x`,
and put `p = f^J x`.
* Case 1: `α p` on the cell itself is impossible (`case_same_face`).
* Case 2: `p` bound: `p` lies on an arc of a region, so the reverse of `d` lies in the loop of
  the first dart of that arc (`case_bound`).
* Case 3: `p` unbound and `α p` on a region: the loop of a side of the region
  (`case_region_face`).
* Case 4: `p` unbound and `α p` on a polygon: `α p` lies in a class of kind `cell i`, the
  reverse of a walk `seg y ℓ` after the pocket.  Either the walk starts at `p`, and the reverse
  of `d` lies in the loop of the class, or the walk wraps around the cell and contains `d`
  (`case_polygon`).  A single class would be a pocket longer than `J` through `d`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

section Ends

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- The end loop of a class: the reverses of the `L` face predecessors of the reverse of its
last dart. -/
noncomputable def classEnd (Q : OsinLemma94ClassPolygons P) (L : ℕ) (k : Fin P.count) (i : ℕ)
    (_ : Bool) : List S.diagram.toCombMap.Dart :=
  (Q.classDarts k i).getLast?.toList.flatMap fun e =>
    back S.diagram.toCombMap (S.diagram.toCombMap.alpha e) L

/-- The end loop of a region: the loops at the side darts and at the first darts of the arcs. -/
noncomputable def regionEnd {X : DiscDiagram.{u, w, v} W} (L : ℕ) (a : RegionCandidate D eps X)
    (_ : Fin 4) : List X.toCombMap.Dart :=
  (a.2.rightSide ++ a.2.leftSide).flatMap (fun z => back X.toCombMap (X.toCombMap.alpha z) L) ++
    (a.2.sourceArc.darts.head?.toList ++ a.2.targetArc.darts.head?.toList).flatMap fun z =>
      back X.toCombMap z L

/-- The covering clause (c) of the end loops input, at budget `L`. -/
def Covered (Q : OsinLemma94ClassPolygons P) (L : ℕ) (d : S.diagram.toCombMap.Dart) : Prop :=
  (∃ k' i', i' < Q.classCount k' ∧ i' ∈ Q.relatorClasses k' ∧
      S.diagram.toCombMap.alpha d ∈ Q.classDarts k' i') ∨
    (∃ k' ∈ Q.budgetPolygons, ∃ i' < Q.classCount k', ∃ b,
      S.diagram.toCombMap.alpha d ∈ classEnd Q L k' i' b) ∨
    ∃ a ∈ S.family, ∃ t, S.diagram.toCombMap.alpha d ∈ regionEnd L a t

theorem length_classEnd (Q : OsinLemma94ClassPolygons P) (L : ℕ) (k : Fin P.count) (i : ℕ)
    (b : Bool) : (classEnd Q L k i b).length ≤ L := by
  have h1 := length_flatMap_le
    (g := fun e => back S.diagram.toCombMap (S.diagram.toCombMap.alpha e) L) (L := L)
    (l := (Q.classDarts k i).getLast?.toList) fun e _ => (length_back _ L).le
  unfold classEnd
  exact h1.trans ((Nat.mul_le_mul_right L Option.length_toList_le).trans (Nat.one_mul L).le)

theorem length_regionEnd {X : DiscDiagram.{u, w, v} W} (L : ℕ) (a : RegionCandidate D eps X)
    (t : Fin 4) : (regionEnd L a t).length ≤ (2 * eps + 2) * L := by
  have h1 := length_flatMap_le (g := fun z => back X.toCombMap (X.toCombMap.alpha z) L)
    (L := L) (l := a.2.rightSide ++ a.2.leftSide) fun z _ => (length_back _ L).le
  have h2 := length_flatMap_le (g := fun z => back X.toCombMap z L) (L := L)
    (l := a.2.sourceArc.darts.head?.toList ++ a.2.targetArc.darts.head?.toList)
    fun z _ => (length_back _ L).le
  rw [List.length_append] at h1 h2
  have hr := a.2.rightSide_length_le
  have hl := a.2.leftSide_length_le
  have hs : a.2.sourceArc.darts.head?.toList.length ≤ 1 := Option.length_toList_le
  have ht : a.2.targetArc.darts.head?.toList.length ≤ 1 := Option.length_toList_le
  rw [regionEnd, List.length_append]
  calc _ ≤ (a.2.rightSide.length + a.2.leftSide.length) * L +
        (a.2.sourceArc.darts.head?.toList.length +
          a.2.targetArc.darts.head?.toList.length) * L := Nat.add_le_add h1 h2
    _ ≤ (2 * eps) * L + 2 * L :=
        Nat.add_le_add (Nat.mul_le_mul_right L (by omega)) (Nat.mul_le_mul_right L (by omega))
    _ = (2 * eps + 2) * L := (Nat.add_mul _ _ _).symm

theorem mem_regionEnd_of_side {X : DiscDiagram.{u, w, v} W} {L : ℕ} (a : RegionCandidate D eps X)
    {z q : X.toCombMap.Dart} (hz : z ∈ a.2.rightSide ++ a.2.leftSide)
    (hq : q ∈ back X.toCombMap (X.toCombMap.alpha z) L) (t : Fin 4) : q ∈ regionEnd L a t := by
  unfold regionEnd
  exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨z, hz, hq⟩))

theorem mem_regionEnd_of_arc {X : DiscDiagram.{u, w, v} W} {L : ℕ} (a : RegionCandidate D eps X)
    {z q : X.toCombMap.Dart}
    (hz : z ∈ a.2.sourceArc.darts.head?.toList ++ a.2.targetArc.darts.head?.toList)
    (hq : q ∈ back X.toCombMap z L) (t : Fin 4) : q ∈ regionEnd L a t := by
  unfold regionEnd
  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨z, hz, hq⟩))

theorem mem_classEnd (Q : OsinLemma94ClassPolygons P) {L : ℕ} {k : Fin P.count} {i : ℕ}
    {e q : S.diagram.toCombMap.Dart} (hlast : (Q.classDarts k i).getLast? = some e)
    (hq : q ∈ back S.diagram.toCombMap (S.diagram.toCombMap.alpha e) L) (b : Bool) :
    q ∈ classEnd Q L k i b := by
  unfold classEnd
  rw [hlast]
  exact List.mem_flatMap.mpr ⟨e, Option.mem_toList.mpr rfl, hq⟩

theorem mem_cellArcDarts_of_source {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}
    (a : RegionCandidate D eps X) {z : X.toCombMap.Dart} (hsi : a.2.source = i)
    (hz : z ∈ a.2.sourceArc.darts) : z ∈ a.cellArcDarts i := by
  refine Finset.mem_union.mpr (Or.inl ?_)
  split
  next => exact List.mem_toFinset.mpr hz
  next hne => exact (hne hsi).elim

theorem mem_cellArcDarts_of_target {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}
    (a : RegionCandidate D eps X) {z : X.toCombMap.Dart} (hti : a.2.target = some i)
    (hz : z ∈ a.2.targetArc.darts) : z ∈ a.cellArcDarts i := by
  refine Finset.mem_union.mpr (Or.inr ?_)
  split
  next => exact List.mem_toFinset.mpr hz
  next hne => exact (hne hti).elim

/-- The reverse of the dart after a pocket is none of the darts of the pocket. -/
theorem sep_alpha {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount} {x : X.toCombMap.Dart}
    {J : ℕ} (hx : IsPocket X i x J) (hJ : 1 ≤ J) (hJn : J < (cellDarts X i).length) :
    ∀ j < J, (X.toCombMap.facePerm ^ j) x ≠ X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x) :=
  fun j hj h => not_reach_pow hx hJ hJn rfl rfl j hj (Relation.EqvGen.rel _ _ (Or.inl h.symm))

/-- **Case 2.**  The dart after the pocket is bound. -/
theorem case_bound {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}
    {family : Finset (RegionCandidate D eps X)} {x d : X.toCombMap.Dart} {J s L : ℕ}
    (hs : s < J) (hd : (X.toCombMap.facePerm ^ s) x = d) (hJL : J ≤ L)
    (hdu : d ∈ RegionCandidate.unboundDarts family i) (hx : x ∈ cellDarts X i)
    (hpu : (X.toCombMap.facePerm ^ J) x ∉ RegionCandidate.unboundDarts family i) :
    ∃ a ∈ family, ∃ st ∈ a.2.sourceArc.darts.head?.toList ++ a.2.targetArc.darts.head?.toList,
      X.toCombMap.alpha d ∈ back X.toCombMap st L := by
  obtain ⟨a, ha, hpa⟩ :=
    OsinUnboundSameCellCount.exists_arc_of_not_mem_unboundDarts (pow_mem_cell hx J) hpu
  rcases mem_cellArcDarts_cases a hpa with ⟨hsrc, hp⟩ | ⟨htgt, hp⟩
  · rcases case_arc hs hd hJL (congrArg (cellDarts X) hsrc) a.2.sourceArc hp with
      hda | ⟨st, hst, hback⟩
    · exact (OsinUnboundSameCellCount.not_mem_unboundDarts_of_mem_cellArcDarts ha
        (mem_cellArcDarts_of_source a hsrc hda) hdu).elim
    · exact ⟨a, ha, st,
        List.mem_append.mpr (Or.inl (Option.mem_toList.mpr (Option.mem_def.mp hst))), hback⟩
  · rcases case_arc hs hd hJL
      ((congrArg (targetDarts X) htgt).trans (rfl : targetDarts X (some i) = cellDarts X i))
      a.2.targetArc hp with hda | ⟨st, hst, hback⟩
    · exact (OsinUnboundSameCellCount.not_mem_unboundDarts_of_mem_cellArcDarts ha
        (mem_cellArcDarts_of_target a htgt hda) hdu).elim
    · exact ⟨a, ha, st,
        List.mem_append.mpr (Or.inr (Option.mem_toList.mpr (Option.mem_def.mp hst))), hback⟩

/-- **Case 3.**  The dart after the pocket is unbound and its reverse lies on a region. -/
theorem case_region_face {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}
    (hvalue : ∀ C ∈ X.relatorCells, RelLetter.listVal C.word ≠ 1)
    {family : Finset (RegionCandidate D eps X)} {x d : X.toCombMap.Dart} {J s L : ℕ}
    (hs : s < J) (hd : (X.toCombMap.facePerm ^ s) x = d) (hJL : J ≤ L)
    (hx : x ∈ cellDarts X i) {a : RegionCandidate D eps X} (ha : a ∈ family)
    (hfa : X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x)) ∈ a.1)
    (hpu : (X.toCombMap.facePerm ^ J) x ∈ RegionCandidate.unboundDarts family i) (t : Fin 4) :
    X.toCombMap.alpha d ∈ regionEnd L a t := by
  rcases case_region hvalue a (pow_mem_cell hx J) hfa with hp | hp
  · exact (OsinUnboundSameCellCount.not_mem_unboundDarts_of_mem_cellArcDarts ha hp hpu).elim
  · exact mem_regionEnd_of_side a hp (alpha_mem_back_p hs hd hJL) t

/-- **Case 4.**  The dart after the pocket is unbound and its reverse lies on an (A1) side. -/
theorem case_polygon (Q : OsinLemma94ClassPolygons P) {i : Fin S.diagram.rCellCount} {L : ℕ}
    (hceil : ∀ y l, IsPocket S.diagram i y l → l ≤ L)
    (hlong : 2 * L + 2 < (cellDarts S.diagram i).length)
    {x d : S.diagram.toCombMap.Dart} {J s : ℕ} (hx : IsPocket S.diagram i x J) (hJ : 1 ≤ J)
    (hJn : J < (cellDarts S.diagram i).length) (hs : s < J)
    (hd : (S.diagram.toCombMap.facePerm ^ s) x = d) (hJL : J ≤ L)
    (hmax : ∀ l', PocketThrough S.diagram i d l' → l' ≤ J)
    (hface : S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ J) x)) ≠
        (cell S.diagram i).face)
    {k' : Fin P.count} {s' : ℕ} {j' : Fin S.diagram.rCellCount} (hs' : s' < P.sideCount k')
    (hj' : P.kind k' s' = .cell j')
    (hps : S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ J) x) ∈
      P.sideDarts k' s') :
    Covered Q L d := by
  obtain ⟨i', hi', hkind, y, ℓ, hy, hℓ, hcl, hpcl⟩ :=
    exists_class Q hs' hj' (pow_mem_cell hx.1 J) hps
  have hpseg : (S.diagram.toCombMap.facePerm ^ J) x ∈ seg S.diagram.toCombMap y ℓ := by
    rw [hcl] at hpcl
    exact mem_of_alpha_mem_reverse_map hpcl
  obtain ⟨t, ht, hpt⟩ := mem_seg_iff.mp hpseg
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hlast0 : (Q.classDarts k' i').getLast? = some (S.diagram.toCombMap.alpha y) := by
    rw [hcl, getLast?_reverse_map_seg]
  obtain ⟨sl, _, hltl, hlast⟩ := getLast?_classDarts Q hi'
  have hymem : S.diagram.toCombMap.alpha y ∈ P.sideDarts k' sl :=
    List.mem_of_getLast? (hlast.symm.trans hlast0)
  have hyface : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) =
      S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ J) x)) :=
    (P.faceOf_of_mem_sideDarts hltl hymem).trans (P.faceOf_of_mem_sideDarts hs' hps).symm
  have hr := reach_across hx rfl rfl hface hyface
  obtain ⟨a, hJa, ha, hay⟩ := outside_index hx hJ hJn rfl rfl hy hr
  rcases wrap_or_start hx.1 hs hd hJa ha hay ht hℓ hpt with ⟨_, haJ⟩ | ⟨hdseg, hJl⟩
  · rw [haJ] at hay
    subst hay
    by_cases h2 : 2 ≤ Q.classCount k'
    · have hrel : i' ∈ Q.relatorClasses k' :=
        show 2 ≤ Q.classCount k' ∧ ∃ j, Q.classKind k' i' = .cell j from ⟨h2, i, hkind⟩
      exact Or.inr (Or.inl ⟨k', Q.mem_budgetPolygons k' i' hi' hrel, i', hi', false,
        mem_classEnd Q hlast0 (alpha_mem_back_p hs hd hJL) false⟩)
    · have hcount : Q.classCount k' = 1 := by omega
      obtain rfl : i' = 0 := by omega
      have hP := single_pocket Q hcount hy hℓ hcl
      have hmL := hceil _ _ hP
      have hl := hmax (J + (m + 1)) ⟨x, s, by omega, hd, hx.append hP (by omega)⟩
      omega
  · have hmem : S.diagram.toCombMap.alpha d ∈ Q.classDarts k' i' := by
      rw [hcl]
      exact alpha_mem_reverse_map hdseg
    by_cases h2 : 2 ≤ Q.classCount k'
    · exact Or.inl ⟨k', i', hi',
        show 2 ≤ Q.classCount k' ∧ ∃ j, Q.classKind k' i' = .cell j from ⟨h2, i, hkind⟩, hmem⟩
    · have hcount : Q.classCount k' = 1 := by omega
      obtain rfl : i' = 0 := by omega
      obtain ⟨t', ht', hyt'⟩ := mem_seg_iff.mp hdseg
      have hl := hmax (m + 1) ⟨y, t', ht', hyt', single_pocket Q hcount hy hℓ hcl⟩
      omega

/-- The walk of the class through the reverse of `d` of a single-class polygon is a pocket
through `d`. -/
theorem exists_pocket_through (Q : OsinLemma94ClassPolygons P) {i : Fin S.diagram.rCellCount}
    {d : S.diagram.toCombMap.Dart} (hdmem : d ∈ cellDarts S.diagram i) {k : Fin P.count}
    {s : ℕ} (hcount : Q.classCount k = 1) (hs : s < P.sideCount k)
    (hrel : s ∈ P.relatorSides k) (hds : S.diagram.toCombMap.alpha d ∈ P.sideDarts k s) :
    ∃ l, PocketThrough S.diagram i d l := by
  obtain ⟨j, hj⟩ : ∃ j : Fin S.diagram.rCellCount, P.kind k s = .cell j := hrel
  obtain ⟨i', hi', _, y, ℓ, hy, hℓ, hcl, hdcl⟩ := exists_class Q hs hj hdmem hds
  obtain rfl : i' = 0 := by omega
  rw [hcl] at hdcl
  obtain ⟨t, ht, hyt⟩ := mem_seg_iff.mp (mem_of_alpha_mem_reverse_map hdcl)
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  exact ⟨m + 1, y, t, ht, hyt, single_pocket Q hcount hy hℓ hcl⟩

/-- **The covering.**  After a longest pocket through an unbound dart off the regions, the
reverse of the dart is covered by a relator class, a class loop or a region loop. -/
theorem covered_of_pocket (Q : OsinLemma94ClassPolygons P)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hlen : ∀ i : Fin S.diagram.rCellCount, 1 < (cellDarts S.diagram i).length)
    (hpv : OsinUnboundSameCellBlocks.PocketValue S.diagram) {L : ℕ}
    {i : Fin S.diagram.rCellCount} (hceil : ∀ y l, IsPocket S.diagram i y l → l ≤ L)
    (hlong : 2 * L + 2 < (cellDarts S.diagram i).length)
    {d x : S.diagram.toCombMap.Dart} {J s : ℕ} (hdoff : d ∈ S.unboundOffRegions i)
    (hx : IsPocket S.diagram i x J) (hs : s < J)
    (hd : (S.diagram.toCombMap.facePerm ^ s) x = d)
    (hmax : ∀ l', PocketThrough S.diagram i d l' → l' ≤ J) : Covered Q L d := by
  have hdu : d ∈ RegionCandidate.unboundDarts S.family i := (Finset.mem_filter.mp hdoff).1
  have hJL : J ≤ L := hceil x J hx
  have hJn : J < (cellDarts S.diagram i).length := by omega
  have hJ : 1 ≤ J := by omega
  by_cases hface : S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ J) x)) =
        (cell S.diagram i).face
  · exact (case_same_face hpv hx hs hd hmax (sep_alpha hx hJ hJn) hface).elim
  by_cases hpu : (S.diagram.toCombMap.facePerm ^ J) x ∈ RegionCandidate.unboundDarts S.family i
  · by_cases hreg : ∃ a ∈ S.family, S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha ((S.diagram.toCombMap.facePerm ^ J) x)) ∈ a.1
    · obtain ⟨a, ha, hfa⟩ := hreg
      exact Or.inr (Or.inr ⟨a, ha, 0, case_region_face hvalue hs hd hJL hx.1 ha hfa hpu 0⟩)
    · obtain ⟨hcell, hout⟩ :=
        S.alpha_faceOf_not_cell_of_unbound hvalue hlen hpu (Ne.symm hface)
      obtain ⟨k', s', hs', hrel', hps⟩ :=
        P.exists_relatorSide_of_unbound hvalue (pow_mem_cell hx.1 J) hcell hout hreg
      obtain ⟨j', hj'⟩ : ∃ j' : Fin S.diagram.rCellCount, P.kind k' s' = .cell j' := hrel'
      exact case_polygon Q hceil hlong hx hJ hJn hs hd hJL hmax hface hs' hj' hps
  · obtain ⟨a, ha, st, hst, hback⟩ := case_bound hs hd hJL hdu hx.1 hpu
    exact Or.inr (Or.inr ⟨a, ha, 0, mem_regionEnd_of_arc a hst hback 0⟩)

end Ends

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops
