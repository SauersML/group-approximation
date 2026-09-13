import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The sides of a polygon of Lemma 9.4 are maximal

Consecutive sides of the walk of an unselected `G`-face (`sidesOf`) of one kind do not run on as
one side: two cell or cutting sides do not continue across one another, two boundary sides do not
continue along `∂Δ`, and two short sides are too long together or do not run along one selected
region.  The walk starts at the first dart of `∂Δ` whenever it passes that dart, so the only break
the walk cannot see falls between its last side and its first.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)

/-- Two consecutive sides of the walk of `f` of one kind break as Lemma 9.4 asks, unless the
second one starts the walk. -/
def SidesBreak (f : S.diagram.toCombMap.Face) (m m' : List S.diagram.toCombMap.Dart) : Prop :=
  S.sideKind m = S.sideKind m' → ∀ e ∈ m.getLast?, ∀ e' ∈ m'.head?,
    ((S.diagram.faceBoundary f).darts.rotate (S.baseOf f)).head? = some e' ∨
      ((S.sideKind m ≠ .short →
          S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e') ≠
            S.diagram.toCombMap.alpha e) ∧
        (S.sideKind m = .short →
          eps < m.length + m'.length ∨
            ¬ ∃ a ∈ S.family, ∀ d ∈ m ++ m',
              S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1))

theorem ne_nil_infix_of_mem_splitSide {g x : List S.diagram.toCombMap.Dart} (hg : g ≠ [])
    (hx : x ∈ S.splitSide g) : x ≠ [] ∧ x <:+: g := by
  unfold splitSide at hx
  split_ifs at hx
  · exact ⟨fun h => PolygonList.nil_notMem_chunks eps g (by subst h; exact hx),
      PolygonList.infix_of_mem_chunks hx⟩
  · rw [List.mem_singleton] at hx
    subst hx
    exact ⟨hg, List.infix_refl _⟩

theorem head?_outerDarts_of_outerPos_eq_zero {e : S.diagram.toCombMap.Dart}
    (he : e ∈ outerDarts S.diagram) (hzero : S.outerPos e = 0) :
    (outerDarts S.diagram).head? = some e := by
  classical
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  have hidx := PolygonList.idxOf_getElem_of_nodup S.outerDarts_nodup i hi
  rw [hie] at hidx
  have hi0 : i = 0 := hidx.symm.trans hzero
  subst hi0
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi, hie]

/-- Inside one group, consecutive short chunks are too long together. -/
theorem splitSide_isChain_break (heps : 1 ≤ eps) {f : S.diagram.toCombMap.Face}
    {g : List S.diagram.toCombMap.Dart} (hg : g ∈ S.groupsOf f) :
    (S.splitSide g).IsChain (S.SidesBreak f) := by
  have hgchain := S.sameSide_chain_of_mem_groupsOf hg
  unfold splitSide
  split_ifs with hshort
  · refine (PolygonList.isChain_chunks heps g).imp_of_mem_imp fun m _ hm _ h => ?_
    intro _ _ _ _ _
    right
    obtain ⟨hlen, hm'ne⟩ := h
    have hmne : m ≠ [] := fun hnil =>
      PolygonList.nil_notMem_chunks eps g (by subst hnil; exact hm)
    have hmkind : S.sideKind m = .short :=
      (S.sideKind_of_infix hgchain hmne (PolygonList.infix_of_mem_chunks hm)).trans hshort
    refine ⟨fun h' => absurd hmkind h', fun _ => Or.inl ?_⟩
    have := List.length_pos_iff.mpr hm'ne
    omega
  · exact List.isChain_singleton g

/-- Between two groups of the walk, the sides break. -/
theorem sidesBreak_of_groups {f : S.diagram.toCombMap.Face}
    {g g' : List S.diagram.toCombMap.Dart} (hg : g ∈ S.groupsOf f) (hg' : g' ∈ S.groupsOf f)
    (ha : g ≠ []) (hb : g' ≠ []) (hbreak : ¬ S.SameSide (g.getLast ha) (g'.head hb)) :
    ∀ x ∈ (S.splitSide g).getLast?, ∀ y ∈ (S.splitSide g').head?, S.SidesBreak f x y := by
  classical
  intro x hx y hy hkind e he e' he'
  have hgchain := S.sameSide_chain_of_mem_groupsOf hg
  have hg'chain := S.sameSide_chain_of_mem_groupsOf hg'
  obtain ⟨hxne, hxinf⟩ := S.ne_nil_infix_of_mem_splitSide ha (List.mem_of_mem_getLast? hx)
  obtain ⟨hyne, hyinf⟩ := S.ne_nil_infix_of_mem_splitSide hb (List.mem_of_mem_head? hy)
  have hex : e ∈ x := List.mem_of_mem_getLast? he
  have hey : e' ∈ y := List.mem_of_mem_head? he'
  rw [PolygonList.getLast?_flatten_of_mem_getLast? (S.nil_notMem_splitSide ha) hx,
    S.flatten_splitSide, List.getLast?_eq_some_getLast ha, Option.mem_def, Option.some_inj] at he
  rw [PolygonList.head?_flatten_of_mem_head? (S.nil_notMem_splitSide hb) hy,
    S.flatten_splitSide, List.head?_eq_some_head hb, Option.mem_def, Option.some_inj] at he'
  have hns : ¬ S.SameSide e e' := by
    rw [← he, ← he']
    exact hbreak
  have hemem : e ∈ g := by
    rw [← he]
    exact List.getLast_mem ha
  have he'mem : e' ∈ g' := by
    rw [← he']
    exact List.head_mem hb
  have hke : S.dartKind e = S.sideKind x :=
    (S.dartKind_eq_sideKind hgchain e hemem).trans (S.sideKind_of_infix hgchain hxne hxinf).symm
  have hke' : S.dartKind e' = S.sideKind x :=
    ((S.dartKind_eq_sideKind hg'chain e' he'mem).trans
      (S.sideKind_of_infix hg'chain hyne hyinf).symm).trans hkind.symm
  have hkee' : S.dartKind e = S.dartKind e' := hke.trans hke'.symm
  have he'face : e' ∈ (S.diagram.faceBoundary f).darts :=
    List.mem_rotate.mp ((S.infix_of_mem_groupsOf hg').subset he'mem)
  by_cases hesc : ((S.diagram.faceBoundary f).darts.rotate (S.baseOf f)).head? = some e'
  · exact Or.inl hesc
  refine Or.inr ⟨fun hns' hback => hns ?_, fun hshort => Or.inr fun hreg => ?_⟩
  · unfold SameSide
    refine ⟨hkee', fun h => absurd (hke.symm.trans h) hns', fun j hj => ?_, fun _ _ => hback⟩
    have hmemO : e ∈ outerDarts S.diagram :=
      S.mem_outerDarts (S.face_alpha_of_dartKind_boundary hj).1
    have hmemO' : e' ∈ outerDarts S.diagram :=
      S.mem_outerDarts (S.face_alpha_of_dartKind_boundary (hkee'.symm.trans hj)).1
    rcases PolygonList.idxOf_eq_succ_or_zero S.outerDarts_ne_nil S.outerDarts_nodup
        S.outerDarts_isChain S.outerDarts_closes
        (fun _ _ _ h h' => S.diagram.toCombMap.alpha_involutive.injective
          (S.diagram.toCombMap.facePerm.injective (h.trans h'.symm)))
        hmemO hback with hsucc | hzero
    · exact hsucc
    · exact absurd (S.head?_rotate_baseOf (S.head?_outerDarts_of_outerPos_eq_zero hmemO' hzero)
        he'face) hesc
  · obtain ⟨a, ha', hall⟩ := hreg
    apply hns
    unfold SameSide
    refine ⟨hkee', fun _ => ?_, fun j hj => ?_, fun h _ => absurd (hke.trans hshort) h⟩
    · exact (S.regionOf_eq_some ha' (hall e (List.mem_append_left _ hex))).trans
        (S.regionOf_eq_some ha' (hall e' (List.mem_append_right _ hey))).symm
    · rw [hke, hshort] at hj
      cases hj

/-- Consecutive sides of the walk break, unless the second one starts the walk. -/
theorem sidesOf_isChain_break (heps : 1 ≤ eps) (f : S.diagram.toCombMap.Face) :
    (S.sidesOf f).IsChain (S.SidesBreak f) := by
  classical
  have hL : [] ∉ (S.groupsOf f).map S.splitSide := by
    intro h
    obtain ⟨g, hg, hsplit⟩ := List.mem_map.mp h
    exact S.ne_nil_of_mem_groupsOf hg (by rw [← S.flatten_splitSide g, hsplit, List.flatten_nil])
  have hgroups : (S.groupsOf f).IsChain fun g g' =>
      ∃ ha hb, decide (S.SameSide (g.getLast ha) (g'.head hb)) = false :=
    List.isChain_getLast_head_splitBy (fun e e' => decide (S.SameSide e e'))
      ((S.diagram.faceBoundary f).darts.rotate (S.baseOf f))
  rw [sidesOf, List.flatMap_def, List.isChain_flatten hL, List.isChain_map]
  refine ⟨fun l hl => ?_, hgroups.imp_of_mem_imp fun g g' hg hg' h => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
    exact S.splitSide_isChain_break heps hg
  · obtain ⟨ha, hb, hbreak⟩ := h
    exact S.sidesBreak_of_groups hg hg' ha hb (of_decide_eq_false hbreak)

/-- **The sides of the walk are maximal**, in the form `OsinLemma94RealizedPolygons.Maximal`
asks of the side list `sidesOf f`. -/
theorem sidesOf_maximal (heps : 1 ≤ eps) (f : S.diagram.toCombMap.Face) (i : ℕ)
    (hi : i + 1 < (S.sidesOf f).length)
    (hkind : S.sideKind ((S.sidesOf f).getD i []) = S.sideKind ((S.sidesOf f).getD (i + 1) [])) :
    ∀ e ∈ ((S.sidesOf f).getD i []).getLast?, ∀ e' ∈ ((S.sidesOf f).getD (i + 1) []).head?,
      (S.sideKind ((S.sidesOf f).getD i []) ≠ .short →
        S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha e') ≠
          S.diagram.toCombMap.alpha e) ∧
      (S.sideKind ((S.sidesOf f).getD i []) = .short →
        eps < ((S.sidesOf f).getD i []).length + ((S.sidesOf f).getD (i + 1) []).length ∨
          ¬ ∃ a ∈ S.family, ∀ d ∈ (S.sidesOf f).getD i [] ++ (S.sidesOf f).getD (i + 1) [],
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1) := by
  intro e he e' he'
  have hi' : i < (S.sidesOf f).length := by omega
  have hx : (S.sidesOf f).getD i [] = (S.sidesOf f)[i]'hi' := List.getD_eq_getElem _ _ hi'
  have hy : (S.sidesOf f).getD (i + 1) [] = (S.sidesOf f)[i + 1]'hi :=
    List.getD_eq_getElem _ _ hi
  rw [hx, hy] at hkind ⊢
  rw [hx] at he
  rw [hy] at he'
  have hL : [] ∉ S.sidesOf f := fun h => (S.side_facts heps h).1 rfl
  have hnodup : (S.sidesOf f).flatten.Nodup := by
    rw [S.flatten_sidesOf]
    exact List.nodup_rotate.mpr (S.diagram.faceBoundary f).nodup
  rcases List.isChain_iff_getElem.mp (S.sidesOf_isChain_break heps f) i hi hkind e he e' he' with
    hesc | h
  · exact absurd (by rw [S.flatten_sidesOf]; exact hesc)
      (PolygonList.head?_flatten_ne_of_lt hL hnodup hi he')
  · exact h

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.sidesBreak_of_groups
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.sidesOf_isChain_break
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.sidesOf_maximal

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen
