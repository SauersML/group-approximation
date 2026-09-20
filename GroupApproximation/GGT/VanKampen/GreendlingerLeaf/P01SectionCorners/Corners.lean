import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.Separation
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactWords
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionExclusion
import GroupApproximation.Meta.AxiomGuard

/-!
# Section corners: every corner sits at a cut and charges a distinct cell

Let `P` be realized polygons of `S`, `X = S.diagram`, `B` the boundary traversal of the outer face
of `X`, `n = |B|`, and `ℓ i` the `i`-th dart of the reversed traversal (`OuterWalk.lean`), so the
oriented outer darts are `α (ℓ i)`.

* `boundary_ends`: a boundary side of section `j` is `α (ℓ a), …, α (ℓ b)` with
  `cut j ≤ a ≤ b < cut (j + 1)` and `b < n`.
* `exists_cornerAt`: a section corner at side `s` of polygon `k` ends a boundary side of section `j`
  at `p = b` and the next side, of section `j' ≠ j`, starts at `q = a'`, with
  `φ (α (ℓ p)) = α (ℓ q)`.  If `j < j'` then `p < cut j' ≤ q`; if `j' < j` then `q < p` and
  `cut 0 ≤ q`.  So some cut position `t` lies in the half-open cyclic interval `(p, q]`
  (`CornerAt`).
* `charge`: a polygon with a cell side `s` (kind `.cell j`) has a dart `x` on its face whose
  reversal lies on the face of cell `j`; the polygon charges the cell `j`.
* `eq_of_cornerAt`: two corners at the same cut position `t` charging the same cell coincide.  If
  the two corner positions `p = p'` agree, the dart `α (ℓ p)` lies on both polygon faces and both
  sides, so the polygons (faces are injective) and sides (side darts are disjoint) coincide.
  Otherwise one of `p, p'` lies in the open interval of the other corner (`inOpen_of_inHalfOpen`)
  and `lobe_separation` excludes a common charged cell.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners

universe u w v

open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The outer traversal has the length of the boundary word. -/
theorem outer_length_eq (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    (S.diagram.faceBoundary S.diagram.outerFace).darts.length = Delta.boundaryWord.length := by
  have h := congrArg List.length (Embedded.dartWord_outerDarts S.diagram)
  rw [S.equiv.boundaryWord_eq] at h
  simpa only [Embedded.dartWord, Embedded.outerDarts, List.length_map, List.length_reverse]
    using h

/-- The darts of an outer arc are the outer darts `α (ℓ i)` at its positions. -/
theorem outerArc_getElem? (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (arc : Embedded.CyclicArc (Embedded.targetDarts S.diagram none)) {i : ℕ}
    (hend : arc.start.1 + arc.length ≤ (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hi : i < arc.length) :
    arc.darts[i]? = some (S.diagram.toCombMap.alpha
      (ell (S.diagram.faceBoundary S.diagram.outerFace) (arc.start.1 + i))) := by
  have hcyc : (Embedded.targetDarts S.diagram none).length =
      (S.diagram.faceBoundary S.diagram.outerFace).darts.length := by
    show (Embedded.outerDarts S.diagram).length = _
    rw [Embedded.outerDarts, List.length_map, List.length_reverse]
  have hlt : arc.start.1 + i < (S.diagram.faceBoundary S.diagram.outerFace).darts.length := by
    omega
  have hdrop : i < ((Embedded.targetDarts S.diagram none).drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  have hrev : arc.start.1 + i <
      (S.diagram.faceBoundary S.diagram.outerFace).darts.reverse.length := by
    rw [List.length_reverse]
    exact hlt
  rw [Embedded.CyclicArc.darts, List.getElem?_take_of_lt hi, Embedded.CyclicArc.rotated,
    List.getElem?_append_left hdrop, List.getElem?_drop]
  show (Embedded.outerDarts S.diagram)[arc.start.1 + i]? = _
  rw [ell_of_lt _ hlt, Embedded.outerDarts, List.getElem?_map, List.getElem?_eq_getElem hrev,
    Option.map_some]

/-- **The ends of a boundary side.** -/
theorem boundary_ends (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s j : ℕ}
    (hs : s < P.sideCount k) (hk : P.kind k s = .boundary j) :
    ∃ hj : j < cuts.count, ∃ a b : ℕ, cuts.cut ⟨j, by omega⟩ ≤ a ∧ a ≤ b ∧
      b < cuts.cut ⟨j + 1, by omega⟩ ∧
      b < (S.diagram.faceBoundary S.diagram.outerFace).darts.length ∧
      (P.sideDarts k s).head? = some (S.diagram.toCombMap.alpha
        (ell (S.diagram.faceBoundary S.diagram.outerFace) a)) ∧
      (P.sideDarts k s).getLast? = some (S.diagram.toCombMap.alpha
        (ell (S.diagram.faceBoundary S.diagram.outerFace) b)) := by
  obtain ⟨hj, arc, hdarts, hstart, hend⟩ := P.boundary_arc k s j hs hk
  have hlast := cuts.cut_mono (Fin.le_last (⟨j + 1, by omega⟩ : Fin (cuts.count + 1)))
  rw [cuts.cut_last, ← outer_length_eq S] at hlast
  have hpos : 0 < arc.length := by
    have h := List.length_pos_iff.mpr (P.side_ne_nil k s hs)
    rwa [hdarts, arc.darts_length] at h
  have hend' :
      arc.start.1 + arc.length ≤ (S.diagram.faceBoundary S.diagram.outerFace).darts.length := by
    omega
  refine ⟨hj, arc.start.1, arc.start.1 + (arc.length - 1), hstart, by omega, by omega, by omega,
    ?_, ?_⟩
  · rw [hdarts, List.head?_eq_getElem?]
    simpa only [Nat.add_zero] using outerArc_getElem? S arc hend' hpos
  · rw [hdarts, List.getLast?_eq_getElem?, arc.darts_length]
    exact outerArc_getElem? S arc hend' (i := arc.length - 1) (by omega)

/-- A corner of polygon side `a` at the outer positions `p`, `q`, around the cut position `t`. -/
def CornerAt (P : OsinLemma94RealizedPolygons S) (a : Σ _ : Fin P.count, ℕ) (t : ℕ) : Prop :=
  ∃ p q : ℕ, p < (S.diagram.faceBoundary S.diagram.outerFace).darts.length ∧
    q < (S.diagram.faceBoundary S.diagram.outerFace).darts.length ∧ InHalfOpen p q t ∧
    a.2 < P.sideCount a.1 ∧
    S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) p) ∈
      P.sideDarts a.1 a.2 ∧
    S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) q) ∈
      P.sideDarts a.1 ((a.2 + 1) % P.sideCount a.1) ∧
    S.diagram.toCombMap.facePerm
        (S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) p)) =
      S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) q)

/-- **Every section corner is a corner at a cut position.** -/
theorem exists_cornerAt (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    (hs : s ∈ P.sectionCorners k) :
    ∃ i : Fin cuts.count, CornerAt P ⟨k, s⟩ (cuts.cut i.castSucc) := by
  obtain ⟨hcont, hbp⟩ := Finset.mem_filter.mp hs
  obtain ⟨⟨j, hkj⟩, ⟨j', hkj'⟩⟩ := hbp
  have hlong : s ∈ P.longTransitions k := (Finset.mem_filter.mp hcont).1
  have hslt : s < P.sideCount k :=
    Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hlong).1).1
  have hnlt : (s + 1) % P.sideCount k < P.sideCount k := Nat.mod_lt _ (by omega)
  have hne := P.kind_ne_next_of_mem_longTransitions hlong
  obtain ⟨hj, a, b, ha, hab, hb, hbn, -, hlastb⟩ := boundary_ends P hslt hkj
  obtain ⟨hj', a', b', ha', hab', hb', hbn', hheada', -⟩ := boundary_ends P hnlt hkj'
  have hface := P.facePerm_getLast_eq_head_mod hslt (Option.mem_def.mpr hlastb)
    (Option.mem_def.mpr hheada')
  have hpmem := List.mem_of_getLast? hlastb
  have hqmem := List.mem_of_mem_head? (Option.mem_def.mpr hheada')
  have hjj : j ≠ j' := by
    rintro rfl
    exact hne (hkj.trans hkj'.symm)
  rcases Nat.lt_or_ge j j' with hlt | hge
  · have hmono : cuts.cut ⟨j + 1, by omega⟩ ≤ cuts.cut ⟨j', by omega⟩ :=
      cuts.cut_mono (Fin.mk_le_mk.mpr (by omega))
    refine ⟨⟨j', hj'⟩, b, a', hbn, by omega, ?_, hslt, hpmem, hqmem, hface⟩
    show InHalfOpen b a' (cuts.cut ⟨j', by omega⟩)
    unfold InHalfOpen
    omega
  · have hmono : cuts.cut ⟨j' + 1, by omega⟩ ≤ cuts.cut ⟨j, by omega⟩ :=
      cuts.cut_mono (Fin.mk_le_mk.mpr (by omega))
    have hzero : cuts.cut ⟨0, by omega⟩ ≤ cuts.cut ⟨j', by omega⟩ :=
      cuts.cut_mono (Fin.mk_le_mk.mpr (by omega))
    refine ⟨⟨0, cuts.count_pos⟩, b, a', hbn, by omega, ?_, hslt, hpmem, hqmem, hface⟩
    show InHalfOpen b a' (cuts.cut ⟨0, by omega⟩)
    unfold InHalfOpen
    omega

/-- A polygon with a cell side has a dart whose reversal lies on that cell. -/
theorem exists_charge (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    (hk : k ∈ P.relatorPolygons) :
    ∃ j : Fin S.diagram.rCellCount, ∃ x : S.diagram.toCombMap.Dart,
      S.diagram.toCombMap.faceOf x = P.face k ∧
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) =
          (Embedded.cell S.diagram j).face := by
  obtain ⟨s, hs, j, hkj⟩ := (Finset.mem_filter.mp hk).2
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (P.side_ne_nil k s hs)
  exact ⟨j, x, P.faceOf_of_mem_sideDarts hs hx,
    ((S.diagram.faceBoundary (Embedded.cell S.diagram j).face).mem_iff _).mp
      (P.alpha_mem_cellDarts_of_mem_cellSideDarts hs hkj hx)⟩

/-- **The cell charged by a polygon.** -/
noncomputable def charge (P : OsinLemma94RealizedPolygons S) (hpos : 0 < S.diagram.rCellCount)
    (k : Fin P.count) : Fin S.diagram.rCellCount :=
  if h : k ∈ P.relatorPolygons then Classical.choose (exists_charge P h) else ⟨0, hpos⟩

theorem charge_spec (P : OsinLemma94RealizedPolygons S) (hpos : 0 < S.diagram.rCellCount)
    {k : Fin P.count} (hk : k ∈ P.relatorPolygons) :
    ∃ x : S.diagram.toCombMap.Dart, S.diagram.toCombMap.faceOf x = P.face k ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) =
        (Embedded.cell S.diagram (charge P hpos k)).face := by
  rw [charge, dif_pos hk]
  exact Classical.choose_spec (exists_charge P hk)

/-- Two half-open intervals containing `t` with distinct left ends: one left end lies in the other
open interval. -/
theorem inOpen_of_inHalfOpen {p q p' q' t : ℕ} (hpp : p ≠ p') (h : InHalfOpen p q t)
    (h' : InHalfOpen p' q' t) : InOpen p q p' ∨ InOpen p' q' p := by
  unfold InHalfOpen at h h'
  unfold InOpen
  omega

/-- A corner and a nested corner position cannot charge the same cell. -/
theorem false_of_inOpen (P : OsinLemma94RealizedPolygons S) (hpos : 0 < S.diagram.rCellCount)
    {a a' : Σ _ : Fin P.count, ℕ} (ha : a.1 ∈ P.relatorPolygons)
    (ha' : a'.1 ∈ P.relatorPolygons) (heq : charge P hpos a.1 = charge P hpos a'.1) {p q p' : ℕ}
    (hpn : p < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hqn : q < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hpn' : p' < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hs : a.2 < P.sideCount a.1)
    (hpmem : S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) p) ∈
      P.sideDarts a.1 a.2)
    (hqmem : S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) q) ∈
      P.sideDarts a.1 ((a.2 + 1) % P.sideCount a.1))
    (hface : S.diagram.toCombMap.facePerm
        (S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) p)) =
      S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) q))
    (hs' : a'.2 < P.sideCount a'.1)
    (hpmem' : S.diagram.toCombMap.alpha (ell (S.diagram.faceBoundary S.diagram.outerFace) p') ∈
      P.sideDarts a'.1 a'.2)
    (h : InOpen p q p') : False := by
  obtain ⟨x, hx, hax⟩ := charge_spec P hpos ha
  obtain ⟨x', hx', hax'⟩ := charge_spec P hpos ha'
  have hnlt : (a.2 + 1) % P.sideCount a.1 < P.sideCount a.1 := Nat.mod_lt _ (by omega)
  have hFp := P.faceOf_of_mem_sideDarts hs hpmem
  have hFq := P.faceOf_of_mem_sideDarts hnlt hqmem
  have hFp' := P.faceOf_of_mem_sideDarts hs' hpmem'
  have hxx : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) =
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x') := by
    rw [hax, hax', heq]
  exact lobe_separation (S.diagram.faceBoundary S.diagram.outerFace) S.diagram.planar
    hpn hqn hpn' hface (by rw [hFp]; exact P.face_ne_outer _)
    (by rw [hFq]; exact P.face_ne_outer _) (by rw [hFp']; exact P.face_ne_outer _) h
    (hx.trans hFp.symm) (hx'.trans hFp'.symm)
    (by rw [hax]; exact (Embedded.cell S.diagram _).face_ne_outer)
    (by rw [hax']; exact (Embedded.cell S.diagram _).face_ne_outer) hxx

/-- **Corners at one cut position charge distinct cells.** -/
theorem eq_of_cornerAt (P : OsinLemma94RealizedPolygons S) (hpos : 0 < S.diagram.rCellCount)
    {a a' : Σ _ : Fin P.count, ℕ} {t : ℕ} (ha : a.1 ∈ P.relatorPolygons)
    (ha' : a'.1 ∈ P.relatorPolygons) (hc : CornerAt P a t) (hc' : CornerAt P a' t)
    (heq : charge P hpos a.1 = charge P hpos a'.1) : a = a' := by
  obtain ⟨p, q, hpn, hqn, hpq, hs, hpmem, hqmem, hface⟩ := hc
  obtain ⟨p', q', hpn', hqn', hpq', hs', hpmem', hqmem', hface'⟩ := hc'
  by_cases hpp : p = p'
  · subst hpp
    obtain ⟨k, s⟩ := a
    obtain ⟨k', s'⟩ := a'
    have hk : k = k' := P.face_injective
      ((P.faceOf_of_mem_sideDarts hs hpmem).symm.trans (P.faceOf_of_mem_sideDarts hs' hpmem'))
    subst hk
    by_cases hss : s = s'
    · rw [hss]
    · exact (P.sideDarts_disjoint k hs hs' hss hpmem hpmem').elim
  · rcases inOpen_of_inHalfOpen hpp hpq hpq' with h | h
    · exact (false_of_inOpen P hpos ha ha' heq hpn hqn hpn' hs hpmem hqmem hface hs' hpmem'
        h).elim
    · exact (false_of_inOpen P hpos ha' ha heq.symm hpn' hqn' hpn hs' hpmem' hqmem' hface' hs
        hpmem h).elim

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.outer_length_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.outerArc_getElem?
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.boundary_ends
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.CornerAt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.exists_cornerAt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.exists_charge
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.charge
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.charge_spec
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.inOpen_of_inHalfOpen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.false_of_inOpen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.eq_of_cornerAt
