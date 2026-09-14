import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonClassHyp
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGonCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.Meta.AxiomGuard

/-!
# The gaps of a two-gon lie on faces of its pocket

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  A two-gon of `phiMapO` with no corner
in its gap bounds a pocket between exterior regions `a` and `b` of one cell.  Its face runs from
the dart `y` of `a` at the outer vertex `O`, through the source crossing of `b` at the cell, and
back.  The rotation of `phiMapO` is the first return of the collapsed face rotation, so between two
consecutive darts of the face at a vertex no dart is retained.

Around `O` the collapsed rotation walks back along `∂Δ`, from the crossing of `b` to that of `a`.
Every dart it passes on the way is not retained, so the face class of `y` holds it and its reverse.
Those reverses are the darts of `∂Δ` in the gap between the target arcs of `a` and `b`, which then
lie on faces of the pocket.

* `faceClassO_pow_of_firstReturn`: a face class holding the end of a run of the collapsed face
  rotation through darts that are not retained holds the whole run.
* `twoGonPocketFace_of_outerGap`: a dart of `∂Δ` after the target arc of `a` and before that of
  `b` lies on a face of the pocket.
* `getElem?_darts_facePerm_pow`, `twoGonPocketFace_of_cellGap`: at the cell the rotation walks
  forward along the source span from the first source dart of `a` to that of `b`, so a dart across
  the gap between their source arcs lies on a face of the pocket.
* `twoGonPocketFace_of_targetSpan`: the outer gap on a target span that starts at `a` and ends
  at `b` without passing the base point.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace Embedded.RegionCandidate

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

private theorem gapIndex_eq_of_getElem?_eq {α : Type*} {l : List α} (hl : l.Nodup) {i j : ℕ}
    {a : α} (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hj''⟩ := List.getElem?_eq_some_iff.mp hj
  exact (hl.getElem_inj_iff).mp hj''.symm

/-- **A face class runs back along a first return.**  If the class holds the dart `m` steps along
the collapsed face rotation from `u`, and no dart strictly in between is retained, then it holds
every dart of the run after `u`. -/
theorem faceClassO_pow_of_firstReturn {x u : (collapsedMap family).Dart} {m : ℕ}
    (hm : FaceClassO family E x (((collapsedMap family).facePerm ^ m) u))
    (hnot : ∀ k, 0 < k → k < m →
      ¬ PhiKeepO family E (((collapsedMap family).facePerm ^ k) u)) :
    ∀ k, 0 < k → k ≤ m → FaceClassO family E x (((collapsedMap family).facePerm ^ k) u) := by
  have key : ∀ d, d < m →
      FaceClassO family E x (((collapsedMap family).facePerm ^ (m - d)) u) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      exact hm
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have hk : ¬ PhiKeepO family E (((collapsedMap family).facePerm ^ (m - (d + 1))) u) :=
        hnot _ (by omega) (by omega)
      have hstep := eqvGen_facePerm_of_not_keep (M := collapsedMap family)
        (keep := PhiKeepO family E) hk
      have hpow : ((collapsedMap family).facePerm ^ (m - d)) u =
          (collapsedMap family).facePerm
            (((collapsedMap family).facePerm ^ (m - (d + 1))) u) := by
        rw [show m - d = m - (d + 1) + 1 by omega, pow_succ', Equiv.Perm.mul_apply]
      rw [hpow] at h1
      exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ hstep)
  intro k hk0 hkm
  have h := key (m - k) (by omega)
  rwa [show m - (m - k) = k by omega] at h

/-- **The outer gap of a two-gon lies on faces of its pocket.**  Let `y` be the dart at `O` of a
two-gon of `phiMapO`, with region `a`, and let `b` be the region two steps on.  A dart of `∂Δ` at
a position after the target arc of `a` and before the start of that of `b`, whose face is neither
the outer face nor cell `i`, lies on a face of the pocket of the face class of `y`. -/
theorem twoGonPocketFace_of_outerGap (P : ExtPhiData family E)
    (hbound : ∀ x ∈ E, x.2.target = none → x.2.targetArc.start.1 + x.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length)
    {y : (phiMapO family E).Dart} (hy : phiCellSideO y = true)
    (hO : sideCellO (phiRegionO y) (phiSideO y) = none)
    (h4 : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y)
    {i : Fin Delta.rCellCount}
    (H : TwoGonClassHyp family E y.1 (phiRegionO y)
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) i)
    {p : ℕ}
    (hp1 : (phiRegionO y).2.targetArc.start.1 + (phiRegionO y).2.targetArc.length ≤ p)
    (hp2 : p < (phiRegionO ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm y))).2.targetArc.start.1)
    (hpL : p < (outerDarts Delta).length)
    (hout : Delta.toCombMap.faceOf ((outerDarts Delta)[p]) ≠ Delta.outerFace)
    (hcell : Delta.toCombMap.faceOf ((outerDarts Delta)[p]) ≠ (cell Delta i).face) :
    TwoGonPocketFace family E y.1 (phiRegionO y)
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)))
      (Delta.toCombMap.faceOf ((outerDarts Delta)[p])) := by
  obtain ⟨hsy, hty⟩ := side_eq_false_of_sideCellO_eq_none hO
  obtain ⟨z, hsz, hz, hzO, hzr⟩ := exists_sigma_eq_of_twoGon P y hy hO h4
  obtain ⟨hszs, htz⟩ := side_eq_false_of_sideCellO_eq_none hzO
  rw [← hzr] at hp2
  have hya := hbound _ (phiRegionO_mem y) hty
  have hyl := (P.nondegenerate _ (phiRegionO_mem y)).2
  have hza := hbound _ (phiRegionO_mem z) htz
  have hzl := (P.nondegenerate _ (phiRegionO_mem z)).2
  have hyB : (Delta.faceBoundary Delta.outerFace).darts[
      (Delta.faceBoundary Delta.outerFace).darts.length - 1 -
        (phiRegionO y).2.targetArc.start.1]? = some y.1.1 := by
    have h := phiO_cross y
    rw [hsy, hy, crossO_false_true_of_eq_none _ hty hyl (by omega)] at h
    exact h
  have hzB : (Delta.faceBoundary Delta.outerFace).darts[
      (Delta.faceBoundary Delta.outerFace).darts.length - 1 -
        (phiRegionO z).2.targetArc.start.1]? = some z.1.1 := by
    have h := phiO_cross z
    rw [hszs, hz, crossO_false_true_of_eq_none _ htz hzl (by omega)] at h
    exact h
  obtain ⟨m, hm0, hmret, hmnot⟩ := (phiMapO_isRestriction family E).sigma_firstReturn z
  rw [hsz] at hmret
  change ((collapsedMap family).facePerm ^ m) z.1 = y.1 at hmret
  have hnk : ∀ k, 0 < k → k < m →
      ¬ PhiKeepO family E (((collapsedMap family).facePerm ^ k) z.1) :=
    fun k hk0 hkm hk => hmnot k hk0 hkm ⟨⟨((collapsedMap family).facePerm ^ k) z.1, hk⟩, rfl⟩
  have hcls := faceClassO_pow_of_firstReturn (family := family) (E := E) (x := y.1) (u := z.1)
    (m := m) (by rw [hmret]; exact Relation.EqvGen.refl _) hnk
  have hpow := outer_collapsed_facePerm_pow P hzB
  have hmk : (phiRegionO z).2.targetArc.start.1 - p < m := by
    by_contra hge
    have hmod := hpow m
    rw [hmret] at hmod
    have hlt : (Delta.faceBoundary Delta.outerFace).darts.length - 1 -
        (phiRegionO z).2.targetArc.start.1 + m <
        (Delta.faceBoundary Delta.outerFace).darts.length := by omega
    rw [Nat.mod_eq_of_lt hlt] at hmod
    have heq := gapIndex_eq_of_getElem?_eq (Delta.faceBoundary Delta.outerFace).nodup hmod hyB
    omega
  have hk0 : 0 < (phiRegionO z).2.targetArc.start.1 - p := by omega
  have hx := hcls _ hk0 hmk.le
  have hkk := hnk _ hk0 hmk
  have hidx := hpow ((phiRegionO z).2.targetArc.start.1 - p)
  have hlt2 : (Delta.faceBoundary Delta.outerFace).darts.length - 1 -
      (phiRegionO z).2.targetArc.start.1 + ((phiRegionO z).2.targetArc.start.1 - p) <
      (Delta.faceBoundary Delta.outerFace).darts.length := by omega
  rw [Nat.mod_eq_of_lt hlt2, show (Delta.faceBoundary Delta.outerFace).darts.length - 1 -
      (phiRegionO z).2.targetArc.start.1 + ((phiRegionO z).2.targetArc.start.1 - p) =
      (Delta.faceBoundary Delta.outerFace).darts.length - 1 - p by omega] at hidx
  obtain ⟨hlt3, hu⟩ := List.getElem?_eq_some_iff.mp hidx
  have hod : (outerDarts Delta)[p] = Delta.toCombMap.alpha
      ((Delta.faceBoundary Delta.outerFace).darts[
        (Delta.faceBoundary Delta.outerFace).darts.length - 1 - p]'hlt3) := by
    simp only [outerDarts, List.getElem_map, List.getElem_reverse]
  have hZ : FaceClassO family E y.1
      ((collapsedMap family).alpha (((collapsedMap family).facePerm ^
        ((phiRegionO z).2.targetArc.start.1 - p)) z.1)) :=
    Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ (Or.inr ⟨hkk, rfl⟩))
  have hval : ((collapsedMap family).alpha (((collapsedMap family).facePerm ^
      ((phiRegionO z).2.targetArc.start.1 - p)) z.1)).1 =
      Delta.toCombMap.alpha (((collapsedMap family).facePerm ^
        ((phiRegionO z).2.targetArc.start.1 - p)) z.1).1 :=
    (collapsedMap_isRestriction family).alpha_map _
  have hface : Delta.toCombMap.faceOf ((collapsedMap family).alpha
      (((collapsedMap family).facePerm ^ ((phiRegionO z).2.targetArc.start.1 - p)) z.1)).1 =
      Delta.toCombMap.faceOf ((outerDarts Delta)[p]) := by
    rw [hval, hod, ← hu]
  have h := P.twoGonPocketFace_of_faceClassO H.mem_left H.mem_right i H.kept_faces
    H.selected_of_source H.nondegenerate hZ (by rw [hface]; exact hout)
    (by rw [hface]; exact hcell)
  rwa [hface] at h

/-- Along a cyclic arc of a face boundary, the dart at position `k` is `k` face steps after the
first dart. -/
theorem getElem?_darts_facePerm_pow {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    (arc : CyclicArc B.darts) {d₀ : M.Dart} (h0 : arc.darts[0]? = some d₀) :
    ∀ k, k < arc.darts.length → arc.darts[k]? = some ((M.facePerm ^ k) d₀) := by
  have hchain : arc.darts.IsChain fun d e => M.facePerm d = e :=
    Embedded.CyclicArc.isChain_darts arc B.chain (fun a ha b hb => by
      rw [Option.mem_def, List.getLast?_eq_some_getLast B.nonempty, Option.some_inj] at ha
      rw [Option.mem_def, List.head?_eq_some_head B.nonempty, Option.some_inj] at hb
      rw [← ha, ← hb]
      exact B.closes)
  intro k
  induction k with
  | zero =>
    intro _
    rw [pow_zero, Equiv.Perm.one_apply]
    exact h0
  | succ k ih =>
    intro hk
    obtain ⟨hk', hdk⟩ := List.getElem?_eq_some_iff.mp (ih (by omega))
    have hstep := (List.isChain_iff_getElem.mp hchain) k hk
    rw [pow_succ', Equiv.Perm.mul_apply, ← hdk, hstep]
    exact List.getElem?_eq_getElem hk

/-- **The cell gap of a two-gon lies on faces of its pocket.**  Let `y` be the dart at `O` of a
two-gon of `phiMapO`, with region `a`, and let `b` be the region two steps on.  If a source span
of the cell of `a` is the source arc of `a`, then `gap`, then the source arc of `b`, every dart
across a dart of `gap` whose face is neither the outer face nor cell `i` lies on a face of the
pocket of the face class of `y`. -/
theorem twoGonPocketFace_of_cellGap (P : ExtPhiData family E)
    {y : (phiMapO family E).Dart} (hy : phiCellSideO y = true)
    (hO : sideCellO (phiRegionO y) (phiSideO y) = none)
    {i : Fin Delta.rCellCount}
    (H : TwoGonClassHyp family E y.1 (phiRegionO y)
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) i)
    (source : CyclicArc (cellDarts Delta (phiRegionO y).2.source))
    {gap : List Delta.toCombMap.Dart}
    (hgap : source.darts = (phiRegionO y).2.sourceArc.darts ++ gap ++
      (phiRegionO ((phiMapO family E).facePerm
        ((phiMapO family E).facePerm y))).2.sourceArc.darts)
    {g : Delta.toCombMap.Dart} (hg : g ∈ gap)
    (hout : Delta.toCombMap.faceOf (Delta.toCombMap.alpha g) ≠ Delta.outerFace)
    (hcell : Delta.toCombMap.faceOf (Delta.toCombMap.alpha g) ≠ (cell Delta i).face) :
    TwoGonPocketFace family E y.1 (phiRegionO y)
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)))
      (Delta.toCombMap.faceOf (Delta.toCombMap.alpha g)) := by
  obtain ⟨hsy, -⟩ := side_eq_false_of_sideCellO_eq_none hO
  have ha1 := P.phiO_alpha y
  have hc1 : phiCellSideO ((phiMapO family E).alpha y) = false := by
    simp only [ha1.2.2, hy, Bool.not_true]
  have hs2 := P.phiO_sigma_of_midpoint ((phiMapO family E).alpha y) hc1
  have hc2 : phiCellSideO ((phiMapO family E).sigma ((phiMapO family E).alpha y)) = false :=
    (P.phiCellSideO_sigma _).trans hc1
  have ha3 := P.phiO_alpha ((phiMapO family E).sigma ((phiMapO family E).alpha y))
  obtain ⟨z, hzdef⟩ : ∃ z : (phiMapO family E).Dart, z = (phiMapO family E).alpha
      ((phiMapO family E).sigma ((phiMapO family E).alpha y)) := ⟨_, rfl⟩
  have hsz : (phiMapO family E).sigma z =
      (phiMapO family E).facePerm ((phiMapO family E).facePerm y) := by
    rw [hzdef]
    rfl
  have hzr : phiRegionO z = phiRegionO y := by
    rw [hzdef]
    exact ha3.1.trans (hs2.1.trans ha1.1)
  have hzs : phiSideO z = true := by
    simp only [hzdef, ha3.2.1, hs2.2, ha1.2.1, hsy, Bool.not_false]
  have hzc : phiCellSideO z = true := by
    simp only [hzdef, ha3.2.2, hc2, Bool.not_false]
  have hzB : (phiRegionO y).2.sourceArc.darts.head? = some z.1.1 := by
    have h := phiO_cross z
    rw [hzs, hzc, hzr, crossO_true] at h
    simpa only [cross, if_true] using h
  have hy2 := sideCellO_facePerm_facePerm P y hy
  have hside2 :
      phiSideO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) = true := by
    cases hs : phiSideO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) with
    | true => rfl
    | false =>
      exfalso
      have h := hy2.2
      rw [hs, hsy] at h
      have h' : (phiRegionO ((phiMapO family E).facePerm
          ((phiMapO family E).facePerm y))).2.target = some (phiRegionO y).2.source := h
      rw [H.target_right] at h'
      cases h'
  have hqB : (phiRegionO ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm y))).2.sourceArc.darts.head? =
      some ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)).1.1 := by
    have hc := phiO_cross ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))
    rw [hside2, hy2.1, crossO_true] at hc
    simpa only [cross, if_true] using hc
  have hlenA : 0 < (phiRegionO y).2.sourceArc.darts.length := by
    rw [CyclicArc.darts_length]
    exact (P.nondegenerate _ (phiRegionO_mem y)).1
  have hlenB : 0 < (phiRegionO ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm y))).2.sourceArc.darts.length := by
    rw [CyclicArc.darts_length]
    exact (P.nondegenerate _ (phiRegionO_mem _)).1
  have hdl : source.darts.length = (phiRegionO y).2.sourceArc.darts.length + gap.length +
      (phiRegionO ((phiMapO family E).facePerm
        ((phiMapO family E).facePerm y))).2.sourceArc.darts.length := by
    rw [hgap, List.length_append, List.length_append]
  have h0 : source.darts[0]? = some z.1.1 := by
    rw [hgap, List.append_assoc, List.getElem?_append_left hlenA, ← List.head?_eq_getElem?]
    exact hzB
  have hn : source.darts[(phiRegionO y).2.sourceArc.darts.length + gap.length]? =
      some ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)).1.1 := by
    rw [hgap, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_right (le_refl _), Nat.sub_self, ← List.head?_eq_getElem?]
    exact hqB
  have hpow : ∀ k, k < source.darts.length →
      source.darts[k]? = some ((Delta.toCombMap.facePerm ^ k) z.1.1) :=
    getElem?_darts_facePerm_pow
      (Delta.faceBoundary (cell Delta (phiRegionO y).2.source).face) source h0
  have hF : ∀ r ∈ family, Delta.toCombMap.faceOf z.1.1 ∉ r.1 := by
    intro r hr
    have hmem : z.1.1 ∈ cellDarts Delta (phiRegionO y).2.source :=
      source.mem_cycle_of_mem_darts (List.mem_of_getElem? h0)
    rw [faceOf_of_mem_cellDarts hmem]
    exact P.cell_not_mem r hr _
  have hval : ∀ k, (((collapsedMap family).facePerm ^ k) z.1).1 =
      (Delta.toCombMap.facePerm ^ k) z.1.1 :=
    fun k => collapsed_pow_val_of_face_not_mem hF k rfl
  obtain ⟨m, hm0, hmret, hmnot⟩ := (phiMapO_isRestriction family E).sigma_firstReturn z
  rw [hsz] at hmret
  change ((collapsedMap family).facePerm ^ m) z.1 =
    ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)).1 at hmret
  have hnk : ∀ k, 0 < k → k < m →
      ¬ PhiKeepO family E (((collapsedMap family).facePerm ^ k) z.1) :=
    fun k hk0 hkm hk => hmnot k hk0 hkm ⟨⟨((collapsedMap family).facePerm ^ k) z.1, hk⟩, rfl⟩
  have hnm : (phiRegionO y).2.sourceArc.darts.length + gap.length ≤ m := by
    by_contra hlt
    have hmidx := hpow m (by omega)
    rw [← hval m, hmret] at hmidx
    have heq := gapIndex_eq_of_getElem?_eq
      (source.darts_nodup (cellDarts_nodup Delta (phiRegionO y).2.source)) hmidx hn
    omega
  have hcl2 : FaceClassO family E y.1
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)).1 :=
    Relation.EqvGen.trans _ _ _ (faceClassO_facePerm y) (faceClassO_facePerm _)
  have hcls := faceClassO_pow_of_firstReturn (family := family) (E := E) (x := y.1) (u := z.1)
    (m := m) (by rw [hmret]; exact hcl2) hnk
  obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
  have hidx : source.darts[(phiRegionO y).2.sourceArc.darts.length + j]? = some g := by
    rw [hgap, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hj, List.getElem?_eq_getElem hj, hgj]
  have hk0 : 0 < (phiRegionO y).2.sourceArc.darts.length + j := by omega
  have hkm : (phiRegionO y).2.sourceArc.darts.length + j < m := by omega
  have hx := hcls _ hk0 hkm.le
  have hkk := hnk _ hk0 hkm
  have hgk : (((collapsedMap family).facePerm ^
      ((phiRegionO y).2.sourceArc.darts.length + j)) z.1).1 = g := by
    have h1 := hpow ((phiRegionO y).2.sourceArc.darts.length + j) (by omega)
    rw [hidx, ← hval] at h1
    exact (Option.some_inj.mp h1).symm
  have hZ : FaceClassO family E y.1
      ((collapsedMap family).alpha (((collapsedMap family).facePerm ^
        ((phiRegionO y).2.sourceArc.darts.length + j)) z.1)) :=
    Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ (Or.inr ⟨hkk, rfl⟩))
  have hvalα : ((collapsedMap family).alpha (((collapsedMap family).facePerm ^
      ((phiRegionO y).2.sourceArc.darts.length + j)) z.1)).1 =
      Delta.toCombMap.alpha (((collapsedMap family).facePerm ^
        ((phiRegionO y).2.sourceArc.darts.length + j)) z.1).1 :=
    (collapsedMap_isRestriction family).alpha_map _
  have hface : Delta.toCombMap.faceOf ((collapsedMap family).alpha
      (((collapsedMap family).facePerm ^
        ((phiRegionO y).2.sourceArc.darts.length + j)) z.1)).1 =
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha g) := by
    rw [hvalα, hgk]
  have h := P.twoGonPocketFace_of_faceClassO H.mem_left H.mem_right i H.kept_faces
    H.selected_of_source H.nondegenerate hZ (by rw [hface]; exact hout)
    (by rw [hface]; exact hcell)
  rwa [hface] at h

/-- **The target gap of a two-gon from the span bounds.**  Let a target span start where the target
arc of `a` starts and end where that of `b` ends, without passing the base point.  Every dart of the
span outside the target arcs of `a` and `b`, whose face is neither the outer face nor cell `i`,
lies on a face of the pocket of the face class of `y`. -/
theorem twoGonPocketFace_of_targetSpan (P : ExtPhiData family E)
    (hbound : ∀ x ∈ E, x.2.target = none → x.2.targetArc.start.1 + x.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length)
    {y : (phiMapO family E).Dart} (hy : phiCellSideO y = true)
    (hO : sideCellO (phiRegionO y) (phiSideO y) = none)
    (h4 : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y)
    {i : Fin Delta.rCellCount}
    (H : TwoGonClassHyp family E y.1 (phiRegionO y)
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) i)
    (target : CyclicArc (targetDarts Delta none))
    (hstart : target.start.1 = (phiRegionO y).2.targetArc.start.1)
    (hend : target.start.1 + target.length =
      (phiRegionO ((phiMapO family E).facePerm
        ((phiMapO family E).facePerm y))).2.targetArc.start.1 +
      (phiRegionO ((phiMapO family E).facePerm
        ((phiMapO family E).facePerm y))).2.targetArc.length)
    (hY : target.start.1 + target.length ≤ (targetDarts Delta none).length)
    (hside : ∀ d ∈ target.darts, Delta.toCombMap.faceOf d ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf d ≠ (cell Delta i).face) :
    ∀ d ∈ target.darts, d ∉ (phiRegionO y).2.targetArc.darts →
      d ∉ (phiRegionO ((phiMapO family E).facePerm
        ((phiMapO family E).facePerm y))).2.targetArc.darts →
      TwoGonPocketFace family E y.1 (phiRegionO y)
        (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)))
        (Delta.toCombMap.faceOf d) := by
  intro d hd hda hdb
  obtain ⟨k, hk, hdk⟩ := List.mem_iff_getElem.mp hd
  have hkl : k < target.length := by rw [← CyclicArc.darts_length]; exact hk
  have hLo : (outerDarts Delta).length = (Delta.faceBoundary Delta.outerFace).darts.length := by
    simp only [outerDarts, List.length_map, List.length_reverse]
  have hYo : target.start.1 + target.length ≤ (outerDarts Delta).length := hY
  have hget' : target.darts[k] =
      (targetDarts Delta none)[target.start.1 + k]'(by omega) := by
    have hdrop : k < ((targetDarts Delta none).drop target.start.1).length := by
      rw [List.length_drop]
      omega
    simp only [CyclicArc.darts, CyclicArc.rotated, List.getElem_take]
    rw [List.getElem_append_left hdrop, List.getElem_drop]
  have hget : target.darts[k] = (outerDarts Delta)[target.start.1 + k]'(by omega) := hget'
  have hA := H.target_left
  have hB := H.target_right
  have hya := hbound _ (phiRegionO_mem y) hA
  have hyb := hbound _ (phiRegionO_mem ((phiMapO family E).facePerm
    ((phiMapO family E).facePerm y))) hB
  have hp1 : (phiRegionO y).2.targetArc.start.1 + (phiRegionO y).2.targetArc.length ≤
      target.start.1 + k := by
    by_contra hlt
    apply hda
    rw [← hdk, hget]
    have hmem := getElem_outerDarts_mem_targetBoundaryDarts Delta (phiRegionO y).2.target
      (phiRegionO y).2.targetArc hA (p := target.start.1 + k) (by omega) (by omega) (by omega)
    rw [targetBoundaryDarts_eq_darts_of_none Delta _ _ hA] at hmem
    exact hmem
  have hp2 : target.start.1 + k < (phiRegionO ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm y))).2.targetArc.start.1 := by
    by_contra hge
    apply hdb
    rw [← hdk, hget]
    have hmem := getElem_outerDarts_mem_targetBoundaryDarts Delta
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))).2.target
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))).2.targetArc hB
      (p := target.start.1 + k) (by omega) (by omega) (by omega)
    rw [targetBoundaryDarts_eq_darts_of_none Delta _ _ hB] at hmem
    exact hmem
  have hsd := hside d hd
  rw [← hdk, hget] at hsd
  rw [← hdk, hget]
  exact twoGonPocketFace_of_outerGap P hbound hy hO h4 H hp1 hp2 (by omega) hsd.1 hsd.2

end Embedded.RegionCandidate

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.faceClassO_pow_of_firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonPocketFace_of_outerGap
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.getElem?_darts_facePerm_pow
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonPocketFace_of_cellGap
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonPocketFace_of_targetSpan
