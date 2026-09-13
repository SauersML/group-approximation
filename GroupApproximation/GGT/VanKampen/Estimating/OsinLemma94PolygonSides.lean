import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonKinds
import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# One side of a polygon of Lemma 9.4

The facts `OsinLemma94RealizedPolygons` asks of one side of the walk of an unselected `G`-face,
for the sides `sidesOf` cut in `OsinLemma94PolygonKinds`: the sides read the walk from its base;
a cell side is an arc of the cell read from across; a boundary side is an arc of `∂Δ` inside one
section; a cutting side has the face on both sides and runs back across itself; a short side runs
along one selected region; and the polygon closes up in `G`.
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

/-! ## The sides read the walk -/

theorem flatten_splitSide (g : List S.diagram.toCombMap.Dart) : (S.splitSide g).flatten = g := by
  unfold splitSide
  split_ifs
  · exact PolygonList.flatten_chunks eps g
  · rw [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem nil_notMem_splitSide {g : List S.diagram.toCombMap.Dart} (hg : g ≠ []) :
    [] ∉ S.splitSide g := by
  unfold splitSide
  split_ifs
  · exact PolygonList.nil_notMem_chunks eps g
  · rw [List.mem_singleton]
    exact fun h => hg h.symm

theorem flatten_flatMap_splitSide :
    ∀ gs : List (List S.diagram.toCombMap.Dart), (gs.flatMap S.splitSide).flatten = gs.flatten
  | [] => by simp only [List.flatMap_nil, List.flatten_nil]
  | g :: gs => by
    rw [List.flatMap_cons, List.flatten_append, S.flatten_splitSide, flatten_flatMap_splitSide gs,
      List.flatten_cons]

theorem flatten_sidesOf (f : S.diagram.toCombMap.Face) :
    (S.sidesOf f).flatten = (S.diagram.faceBoundary f).darts.rotate (S.baseOf f) := by
  rw [sidesOf, S.flatten_flatMap_splitSide, groupsOf, List.flatten_splitBy]

theorem baseOf_le (f : S.diagram.toCombMap.Face) :
    S.baseOf f ≤ (S.diagram.faceBoundary f).darts.length := by
  classical
  unfold baseOf
  cases (outerDarts S.diagram).head? with
  | none => exact Nat.zero_le _
  | some e => exact List.idxOf_le_length

/-- If the walk passes the first dart of `∂Δ`, it starts there. -/
theorem head?_rotate_baseOf {f : S.diagram.toCombMap.Face} {e : S.diagram.toCombMap.Dart}
    (he : (outerDarts S.diagram).head? = some e) (hmem : e ∈ (S.diagram.faceBoundary f).darts) :
    ((S.diagram.faceBoundary f).darts.rotate (S.baseOf f)).head? = some e := by
  classical
  have hb : S.baseOf f = (S.diagram.faceBoundary f).darts.idxOf e := by
    unfold baseOf
    rw [he]
    rfl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  rw [hb, PolygonList.idxOf_getElem_of_nodup (S.diagram.faceBoundary f).nodup i hi,
    List.head?_rotate hi, List.getElem?_eq_getElem hi]

theorem face_of_mem_rotate {f : S.diagram.toCombMap.Face} {r : ℕ} {d : S.diagram.toCombMap.Dart}
    (hd : d ∈ (S.diagram.faceBoundary f).darts.rotate r) : S.diagram.toCombMap.faceOf d = f :=
  ((S.diagram.faceBoundary f).mem_iff d).mp (List.mem_rotate.mp hd)

theorem flatMap_dartWord :
    ∀ sides : List (List S.diagram.toCombMap.Dart),
      sides.flatMap (dartWord S.diagram) = dartWord S.diagram sides.flatten
  | [] => by simp only [List.flatMap_nil, List.flatten_nil, dartWord, List.map_nil]
  | m :: sides => by
    rw [List.flatMap_cons, flatMap_dartWord sides, List.flatten_cons]
    simp only [dartWord, List.map_append]

/-- The polygon closes up in `G`. -/
theorem listVal_sidesOf {f : S.diagram.toCombMap.Face} (hf : S.UnselectedGFace f) :
    RelLetter.listVal ((List.range (S.sidesOf f).length).flatMap fun i =>
      dartWord S.diagram ((S.sidesOf f).getD i [])) = 1 := by
  rw [PolygonList.range_flatMap_getD (S.sidesOf f) (dartWord S.diagram), S.flatMap_dartWord,
    S.flatten_sidesOf, dartWord, List.map_rotate]
  refine PinchSplit.listVal_rotate_eq_one_of_eq_one _
    (by rw [List.length_map]; exact S.baseOf_le f) ?_
  rcases S.diagram.inner_face f hf.1 with ⟨C, hC, hface⟩ | h
  · exact absurd hface (hf.2.1 C hC)
  · exact h

/-! ## Groups and sides -/

theorem sameSide_chain_of_mem_groupsOf {f : S.diagram.toCombMap.Face}
    {g : List S.diagram.toCombMap.Dart} (hg : g ∈ S.groupsOf f) : g.IsChain S.SameSide := by
  classical
  exact (List.isChain_of_mem_splitBy hg).imp_of_mem_imp fun _ _ _ _ h => of_decide_eq_true h

theorem ne_nil_of_mem_groupsOf {f : S.diagram.toCombMap.Face} {g : List S.diagram.toCombMap.Dart}
    (hg : g ∈ S.groupsOf f) : g ≠ [] := by
  rintro rfl
  exact List.nil_notMem_splitBy _ _ hg

theorem infix_of_mem_groupsOf {f : S.diagram.toCombMap.Face} {g : List S.diagram.toCombMap.Dart}
    (hg : g ∈ S.groupsOf f) : g <:+: (S.diagram.faceBoundary f).darts.rotate (S.baseOf f) := by
  have h := List.infix_of_mem_flatten hg
  rwa [groupsOf, List.flatten_splitBy] at h

/-- Along a side, the kind is constant. -/
theorem dartKind_eq_sideKind {m : List S.diagram.toCombMap.Dart} (hm : m.IsChain S.SameSide) :
    ∀ d ∈ m, S.dartKind d = S.sideKind m := by
  cases m with
  | nil => intro d hd; cases hd
  | cons x t =>
    exact List.IsChain.induction (fun d => S.dartKind d = S.dartKind x) (x :: t) hm
      (by intro a b h ha; exact h.1.symm.trans ha) (fun _ => rfl)

/-- Along a short side, the selected region across is constant. -/
theorem regionOf_eq_of_isChain {x : S.diagram.toCombMap.Dart} {t : List S.diagram.toCombMap.Dart}
    (hm : (x :: t).IsChain S.SameSide) (hx : S.dartKind x = .short) :
    ∀ d ∈ x :: t, S.regionOf d = S.regionOf x := by
  have h := List.IsChain.induction
    (fun d => S.dartKind d = .short ∧ S.regionOf d = S.regionOf x) (x :: t) hm
    (by intro a b h ha; exact ⟨h.1.symm.trans ha.1, (h.2.1 ha.1).symm.trans ha.2⟩)
    (fun _ => ⟨hx, rfl⟩)
  exact fun d hd => (h d hd).2

theorem sideKind_of_infix {g m : List S.diagram.toCombMap.Dart} (hg : g.IsChain S.SameSide)
    (hm : m ≠ []) (hinf : m <:+: g) : S.sideKind m = S.sideKind g := by
  cases m with
  | nil => exact absurd rfl hm
  | cons d t => exact S.dartKind_eq_sideKind hg d (hinf.subset (List.mem_cons_self ..))

/-- A side is a nonempty infix of the walk, one side throughout, and short sides have length at
most `ε`. -/
theorem side_facts (heps : 1 ≤ eps) {f : S.diagram.toCombMap.Face}
    {m : List S.diagram.toCombMap.Dart} (hm : m ∈ S.sidesOf f) :
    m ≠ [] ∧ m <:+: (S.diagram.faceBoundary f).darts.rotate (S.baseOf f) ∧
      m.IsChain S.SameSide ∧ (S.sideKind m = .short → m.length ≤ eps) := by
  obtain ⟨g, hg, hmg⟩ := List.mem_flatMap.mp hm
  have hgne := S.ne_nil_of_mem_groupsOf hg
  have hgchain := S.sameSide_chain_of_mem_groupsOf hg
  have hginf := S.infix_of_mem_groupsOf hg
  unfold splitSide at hmg
  split_ifs at hmg with hshort
  · have hinf := PolygonList.infix_of_mem_chunks hmg
    refine ⟨fun h => PolygonList.nil_notMem_chunks eps g (by subst h; exact hmg), hinf.trans hginf,
      hgchain.infix hinf, fun _ => PolygonList.length_le_of_mem_chunks heps g m hmg⟩
  · rw [List.mem_singleton] at hmg
    subst hmg
    exact ⟨hgne, hginf, hgchain, fun h => absurd h hshort⟩

/-! ## The side fields -/

/-- Off the exterior and the selected regions, the walk across a side runs back along it. -/
theorem backChain_of_side {m : List S.diagram.toCombMap.Dart} (hm : m.IsChain S.SameSide)
    (hns : S.sideKind m ≠ .short) (hnb : ∀ j, S.sideKind m ≠ .boundary j) :
    m.IsChain fun x y =>
      S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha y) = S.diagram.toCombMap.alpha x :=
  hm.imp_of_mem_imp fun a _ ha _ h =>
    h.2.2.2 (by rw [S.dartKind_eq_sideKind hm a ha]; exact hns)
      (fun j => by rw [S.dartKind_eq_sideKind hm a ha]; exact hnb j)

theorem cell_arc_of_side {m : List S.diagram.toCombMap.Dart} (hm : m.IsChain S.SameSide)
    (hnodup : m.Nodup) {j : Fin S.diagram.rCellCount} (hkind : S.sideKind m = .cell j) :
    ∃ arc : CyclicArc (cellDarts S.diagram j), m = arc.reverseDarts := by
  have hinv : ∀ x, S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha x) = x :=
    S.diagram.toCombMap.alpha_involutive
  have hk : ∀ d ∈ m, S.dartKind d = .cell j := fun d hd =>
    (S.dartKind_eq_sideKind hm d hd).trans hkind
  have hback := S.backChain_of_side hm (by rw [hkind]; exact fun h => by cases h)
    (fun _ => by rw [hkind]; exact fun h => by cases h)
  obtain ⟨arc, harc⟩ : ∃ arc : CyclicArc (cellDarts S.diagram j),
      arc.darts = (m.map S.diagram.toCombMap.alpha).reverse :=
    PolygonList.exists_cyclicArc_of_isChain
    (r := fun d e => S.diagram.toCombMap.facePerm d = e)
    (S.diagram.faceBoundary (cell S.diagram j).face).nonempty
    (S.diagram.faceBoundary (cell S.diagram j).face).chain
    (S.diagram.faceBoundary (cell S.diagram j).face).closes
    (fun _ _ _ h h' => h.symm.trans h') (t := (m.map S.diagram.toCombMap.alpha).reverse)
    (by rw [List.isChain_reverse, List.isChain_map]; exact hback)
    (List.nodup_reverse.mpr (hnodup.map S.diagram.toCombMap.alpha_involutive.injective))
    (by
      intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hd)
      exact ((S.diagram.faceBoundary _).mem_iff _).mpr
        (S.face_alpha_of_dartKind_cell (hk e he)).symm)
  refine ⟨arc, ?_⟩
  rw [CyclicArc.reverseDarts, harc, List.reverse_reverse, List.map_map]
  conv_lhs => rw [← List.map_id m]
  exact List.map_congr_left fun d _ => (hinv d).symm

theorem boundary_arc_of_side {m : List S.diagram.toCombMap.Dart} (hm : m.IsChain S.SameSide)
    (hne : m ≠ []) {j : ℕ} (hkind : S.sideKind m = .boundary j) :
    ∃ hj : j < cuts.count, ∃ arc : CyclicArc (targetDarts S.diagram none),
      m = arc.darts ∧ cuts.cut ⟨j, by omega⟩ ≤ arc.start.1 ∧
        arc.start.1 + arc.length ≤ cuts.cut ⟨j + 1, by omega⟩ := by
  classical
  have hk : ∀ d ∈ m, S.dartKind d = .boundary j := fun d hd =>
    (S.dartKind_eq_sideKind hm d hd).trans hkind
  have hsec : ∀ d ∈ m, j = PolygonList.sectionIndex cuts.cut (S.outerPos d) := fun d hd =>
    (S.face_alpha_of_dartKind_boundary (hk d hd)).2
  have hmemO : ∀ d ∈ m, d ∈ outerDarts S.diagram := fun d hd =>
    S.mem_outerDarts (S.face_alpha_of_dartKind_boundary (hk d hd)).1
  obtain ⟨arc, harc, hpos⟩ := PolygonList.exists_cyclicArc_of_isChain_idxOf S.outerDarts_nodup
    hmemO (hm.imp_of_mem_imp fun a _ ha _ h => h.2.2.1 j (hk a ha))
  have hcount := cuts.count_pos
  have hzero : PolygonList.cutAt cuts.cut 0 = 0 := by
    rw [PolygonList.cutAt_of_lt (j := 0) cuts.cut (by omega)]
    exact cuts.cut_zero
  have hlast : PolygonList.cutAt cuts.cut cuts.count = Delta.boundaryWord.length :=
    (PolygonList.cutAt_of_lt (j := cuts.count) cuts.cut (Nat.lt_succ_self _)).trans cuts.cut_last
  have hlen := CyclicArc.darts_length arc
  rw [harc] at hlen
  have hmlen : 0 < m.length := List.length_pos_iff.mpr hne
  have hl1 : m.length - 1 < m.length := by omega
  have h0 : S.outerPos m[0] = arc.start.1 + 0 := hpos 0 hmlen
  have hl : S.outerPos m[m.length - 1] = arc.start.1 + (m.length - 1) := hpos _ hl1
  have hj0 := hsec _ (List.getElem_mem hmlen)
  have hjl := hsec _ (List.getElem_mem hl1)
  have hlt : S.outerPos m[m.length - 1] < PolygonList.cutAt cuts.cut cuts.count := by
    rw [hlast, ← S.length_outerDarts]
    exact List.idxOf_lt_length_iff.mpr (hmemO _ (List.getElem_mem _))
  have hjcount : j < cuts.count := by
    rw [hj0]
    exact PolygonList.sectionIndex_lt hcount cuts.cut _
  refine ⟨hjcount, arc, harc.symm, ?_, ?_⟩
  · have h := PolygonList.cutAt_sectionIndex_le cuts.cut hzero (S.outerPos m[0])
    rw [← hj0, PolygonList.cutAt_of_lt (j := j) cuts.cut (by omega), h0] at h
    omega
  · have h := PolygonList.lt_cutAt_sectionIndex_succ hcount cuts.cut hlt
    rw [← hjl, PolygonList.cutAt_of_lt (j := j + 1) cuts.cut (by omega), hl] at h
    omega

theorem short_region_of_side {m : List S.diagram.toCombMap.Dart} (hm : m.IsChain S.SameSide)
    (hne : m ≠ []) (hkind : S.sideKind m = .short) :
    ∃ a ∈ S.family, ∀ d ∈ m,
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1 := by
  cases m with
  | nil => exact absurd rfl hne
  | cons x t =>
    obtain ⟨a, ha, hx⟩ := S.exists_region_of_dartKind_short (d := x) hkind
    refine ⟨a, ha, fun d hd => (S.regionOf_spec ?_).2⟩
    rw [S.regionOf_eq_of_isChain hm hkind d hd]
    exact S.regionOf_eq_some ha hx

theorem short_of_side {m : List S.diagram.toCombMap.Dart} (hlen : m.length ≤ eps) :
    HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (dartWord S.diagram m) ∧
      (dartWord S.diagram m).length ≤ eps := by
  refine ⟨fun a ha => ?_, by rw [dartWord, List.length_map]; exact hlen⟩
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
  exact S.label_admissible d

/-- A cutting side has the face on both sides. -/
theorem cutting_internal_of_side (hapart : S.GFacesApart) {f : S.diagram.toCombMap.Face}
    (hf : S.UnselectedGFace f) {m : List S.diagram.toCombMap.Dart} (hm : m.IsChain S.SameSide)
    (hsub : ∀ d ∈ m, S.diagram.toCombMap.faceOf d = f) (hkind : S.sideKind m = .cutting) :
    ∀ d ∈ m, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = f := by
  intro d hd
  have hu := S.unselected_of_dartKind_cutting ((S.dartKind_eq_sideKind hm d hd).trans hkind)
  rw [← hsub d hd] at hf ⊢
  exact (hapart d hf hu).symm

theorem quasiGeodesic_of_side (hapart : S.GFacesApart) (hcell : S.CellArcsQuasiGeodesic)
    (hbd : S.BoundaryArcsQuasiGeodesic) (hcut : S.CuttingChainsQuasiGeodesic)
    {f : S.diagram.toCombMap.Face} (hf : S.UnselectedGFace f) {m : List S.diagram.toCombMap.Dart}
    (hm : m.IsChain S.SameSide) (hne : m ≠ []) {r : ℕ}
    (hinf : m <:+: (S.diagram.faceBoundary f).darts.rotate r) (hkind : S.sideKind m ≠ .short) :
    IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2)
      (dartWord S.diagram m) := by
  have hnodup : m.Nodup :=
    (List.nodup_rotate.mpr (S.diagram.faceBoundary f).nodup).sublist hinf.sublist
  have hsub : ∀ d ∈ m, S.diagram.toCombMap.faceOf d = f := fun d hd =>
    S.face_of_mem_rotate (hinf.subset hd)
  cases hk : S.sideKind m with
  | cell j =>
    obtain ⟨arc, rfl⟩ := S.cell_arc_of_side hm hnodup hk
    exact hcell j arc
  | boundary j =>
    obtain ⟨hj, arc, rfl, h1, h2⟩ := S.boundary_arc_of_side hm hne hk
    exact hbd j hj arc h1 h2
  | cutting =>
    have hback := S.backChain_of_side hm (by rw [hk]; exact fun h => by cases h)
      (fun _ => by rw [hk]; exact fun h => by cases h)
    obtain ⟨s, t, hst⟩ := hinf
    refine hcut f (r + s.length) m (t ++ s) hf ?_ (S.cutting_internal_of_side hapart hf hm hsub hk)
      (S.runsBackAcross_of_isChain hback)
    rw [← List.rotate_rotate, ← hst, List.append_assoc, List.rotate_append_length_eq,
      List.append_assoc]
  | short => exact absurd hk hkind

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.listVal_sidesOf
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.side_facts
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.cell_arc_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.boundary_arc_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.short_region_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.quasiGeodesic_of_side

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen
