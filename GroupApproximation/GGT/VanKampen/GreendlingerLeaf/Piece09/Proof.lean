import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoArcSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFaceSetOnCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketInnerWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.Estimating.RegionProfileTransport
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningRegions
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.Facts
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.Arcs
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 09: the two-arc face set producer on a whole section

`GreendlingerLeaf.Piece09.proof` proves `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`.

On the copy of `PocketFaceSetOnCopy.exists_copyClean`, two distinct exterior regions `x`, `y` of a
cell `Π` to one section give the pocket walk `s_1 t_1⁻¹ s_2 t_2` and its face set `P`
(`PocketWalk.exists_pocketFaceSet_of_exteriorAt`, with the kept cell from `sectionPocketKeptCell`).
Here `s_1 = l_y`, `s_2 = r_x`, `t_1 = u_x · Gap · u_y` and `t_2` starts with the target arc `t_x`.

Cutting the region `x` off `P` leaves the face set `P \ x` with boundary cycle
`l_y · (Gap · u_y)⁻¹ · l_x⁻¹ · β`, where `β` is `t_2` after `t_x`:

* `walk_off_region`, `region_subset_pocket`: the region `x` lies inside `P`;
* `leftSide_not_mem_walk`: the left side of `x` is off the pocket walk;
* `exists_source_split`, `exists_target_split`: the arcs `Gap · u_y` and `β`, proper since `u_x` and
  `t_x` are nonempty;
* `exists_twoArc_of_pocket`: the face set `P \ x` in walk order, with both arcs proper.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

universe u w v

open Embedded SimpleClosedWalkSides
open scoped Classical

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- A pocket face set whose boundary cycle is a closed dart path is in walk order. -/
theorem closedWalk_of_closedPath {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
    (Q : PocketFaceSet D eps X lo hi)
    (h : ∃ p, DartPath X.toCombMap p p Q.boundary.cycle) : Q.ClosedWalk := by
  obtain ⟨p, hp⟩ := h
  exact closedWalk_of_dartPath X.toCombMap Q.boundary.cycle p hp Q.boundary.cycle_nonempty

/-- The face of a dart whose reverse lies on the boundary cycle of a pocket is off the pocket. -/
theorem cell_not_mem_pocket {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
    (P : PocketFaceSet D eps X lo hi) {s : X.toCombMap.Dart}
    (hs : X.toCombMap.alpha s ∈ P.boundary.cycle) : X.toCombMap.faceOf s ∉ P.faces := by
  have h : X.toCombMap.faceOf (X.toCombMap.alpha s) ∈ P.faces ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha s)) ∉ P.faces :=
    (P.boundary.cycle_mem_iff _).mp hs
  rw [X.toCombMap.alpha_involutive s] at h
  exact h.2

/-- **The cut pocket.**  A boundary cycle `s_1 σ⁻¹ s_2 β` of `P \ Rx`, in walk order, with the kept
cell of `P` off `Rx` and proper arcs, gives the two-arc face set. -/
theorem pocket_of_cut {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} {Rx : Finset X.toCombMap.Face}
    (P : PocketFaceSet D eps X lo hi)
    (Bc : Surgery.MapCollapse.BoundaryCycle X.toCombMap (P.faces \ Rx))
    (source : Fin X.rCellCount) (σ : CyclicArc (cellDarts X source))
    (β : CyclicArc (outerDarts X)) (first second : List X.toCombMap.Dart)
    (hBc : Bc.cycle = first ++ invDarts X σ.darts ++ second ++ β.darts)
    (hclosed : ∃ p, DartPath X.toCombMap p p Bc.cycle)
    (hsrcN : (cell X source).face ∉ P.faces) (hkeptR : (cell X P.kept).face ∉ Rx)
    (hf : first.length ≤ eps) (hs : second.length ≤ eps)
    (hfn : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X first)) ≤ eps)
    (hsn : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X second)) ≤ eps)
    (hlo : lo ≤ β.start.1) (hhi : β.start.1 + β.length ≤ hi)
    (hσ : σ.length < (cellDarts X source).length) (hβ : β.length < (outerDarts X).length) :
    ∃ K : PocketFaceSet D eps X lo hi, K.ClosedWalk ∧
      K.sourceArc.length < (cellDarts X K.source).length ∧
        K.targetArc.length < (outerDarts X).length :=
  ⟨PocketFaceSet.ofBoundaryCycleOfNotMem Bc source P.kept σ β first second hBc
      (fun h => P.outerFace_not_mem (Finset.mem_sdiff.mp h).1)
      (fun h => hsrcN (Finset.mem_sdiff.mp h).1)
      (Finset.mem_sdiff.mpr ⟨P.kept_mem, hkeptR⟩) hf hs hfn hsn hlo hhi,
    closedWalk_of_closedPath _ hclosed, hσ, hβ⟩

/-- **The source split.**  If the source arc of a pocket walk lists a nonempty `xs` and then `zs`,
the darts `zs` form a proper arc of the source cell. -/
theorem exists_source_split {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
    (K : PocketWalk D eps X lo hi) {xs zs : List X.toCombMap.Dart} (hxs : xs ≠ [])
    (hsrc : K.sourceArc.darts = xs ++ zs) :
    ∃ σ : CyclicArc (cellDarts X K.source), σ.darts = zs ∧
      σ.length < (cellDarts X K.source).length := by
  have hlen := K.sourceArc.darts_length
  rw [hsrc, List.length_append] at hlen
  have hpos : 0 < xs.length := by
    cases xs with
    | nil => exact absurd rfl hxs
    | cons _ _ => exact Nat.succ_pos _
  have hle := K.sourceArc.length_le
  obtain ⟨σ, hσl, hσd, -⟩ := exists_suffixArc K.sourceArc xs.length (by omega)
  refine ⟨σ, ?_, ?_⟩
  · rw [hσd, hsrc]
    exact List.drop_left' rfl
  · omega

/-- **The walk split.**  The pocket walk reads `l_y (Gap u_y)⁻¹ · u_x⁻¹ r_x t_x · β`. -/
theorem walk_eq_split {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ} {i : Fin X.rCellCount}
    {x y : RegionCandidate D eps X} (K : PocketWalk D eps X lo hi)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (Gap : CyclicArc (cellDarts X i)) (β : CyclicArc (outerDarts X))
    (hsrc : K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (htgt : K.targetArc.darts = x.2.targetArc.darts ++ β.darts) :
    K.walk = (y.2.leftSide ++ invDarts X (Gap.darts ++ y.2.sourceArc.darts)) ++
      (invDarts X x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts) ++ β.darts := by
  simp only [PocketWalk.walk, hfirst, hsecond, hsrc, htgt, invDarts, List.reverse_append,
    List.map_append, List.append_assoc]

/-- **The left side of `x` is off the pocket walk.** -/
theorem leftSide_not_mem_walk {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
    {x y : RegionCandidate D eps X} (K : PocketWalk D eps X lo hi) (hxt : x.2.target = none)
    (hdisj : Disjoint x.1 y.1) (hfirst : K.firstSide = y.2.leftSide)
    (hsecond : K.secondSide = x.2.rightSide) (hc' : K.CopyClean y x) :
    ∀ l ∈ x.2.leftSide, l ∉ K.walk := by
  intro l hl hw
  have hbd := (region_mem_iff x hxt l).mp (List.mem_append_right _ hl)
  have hnd := x.2.boundary.cycle_nodup
  rw [region_cycle_eq x hxt] at hnd
  rcases PocketWalk.mem_walk_cases K hw with h | h | h | h
  · rw [hfirst] at h
    have hy : X.toCombMap.faceOf l ∈ y.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha l) ∉ y.1 :=
      (y.2.boundary.cycle_mem_iff l).mp (by
        rw [y.2.boundary_decomposition]
        exact List.mem_append_right _ h)
    exact Finset.disjoint_left.mp hdisj hbd.1 hy.1
  · exact hc'.side_cell l (List.mem_append_left _ hl)
      (PocketWalk.faceOf_alpha_of_mem_invDarts_sourceArc K h)
  · rw [hsecond] at h
    exact (List.nodup_append.mp hnd).2.2 l
      (List.mem_append_left _ (List.mem_append_right _ h)) l hl rfl
  · exact hc'.side_outer l (List.mem_append_left _ hl)
      (PocketWalk.faceOf_alpha_of_mem_targetArc K h)

/-- **The region is inside the pocket.**  If the pocket walk crosses no edge inside `x` and meets
`x` from outside along a dart, every face of `x` lies in the pocket. -/
theorem region_subset_pocket {X : DiscDiagram.{u, w, v} W} {lo hi lo' hi' : ℕ}
    {x : RegionCandidate D eps X} (K : PocketWalk D eps X lo hi)
    (P : PocketFaceSet D eps X lo' hi') (hPw : P.boundary.cycle = K.walk)
    (hoff : ∀ e ∈ K.walk, X.toCombMap.faceOf e ∈ x.1 →
      X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ x.1)
    {s : X.toCombMap.Dart} (hsin : X.toCombMap.faceOf (X.toCombMap.alpha s) ∈ x.1)
    (hswalk : X.toCombMap.alpha s ∈ K.walk) : x.1 ⊆ P.faces := by
  have h : ∀ d, d ∈ K.walk ↔
      X.toCombMap.faceOf d ∈ P.faces ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ P.faces :=
    fun d => by
      rw [← hPw]
      exact P.boundary.cycle_mem_iff d
  intro g hg
  exact (PocketWalkColour.mem_iff_of_faceSetBoundary (not_iff_iff_walkKeep h) x.2.boundary hoff
    hsin hg).mp ((h _).mp hswalk).1

end Pocket

section Section

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- The pocket walk crosses no edge inside an exterior region `x` of its source cell. -/
theorem walk_off_region (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i) (hdisj : Disjoint x.1 y.1) {lo hi : ℕ}
    (K : PocketWalk D eps S.diagram lo hi) (hsource : K.source = i)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide) :
    ∀ e ∈ K.walk, S.diagram.toCombMap.faceOf e ∈ x.1 →
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ x.1 := by
  intro e he hex
  rcases PocketWalkColour.walk_cases K hsource hfirst hsecond he with h | h | h | h
  · exact h.2
  · exact absurd h.1 (Finset.disjoint_left.mp hdisj hex)
  · rw [h]
    exact PocketWalkColour.cell_face_not_mem S hx
  · rw [h]
    exact fun hmem => (x.2.boundary.all_gCells _ hmem).1 rfl

/-- A source dart of `x` whose reverse lies on the pocket walk. -/
theorem exists_sourceDart_walk (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i) {lo hi : ℕ}
    (K : PocketWalk D eps S.diagram lo hi) (Gap : CyclicArc (cellDarts S.diagram i))
    (hsrc : K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) :
    ∃ s, S.diagram.toCombMap.faceOf s = (cell S.diagram i).face ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha s) ∈ x.1 ∧
        S.diagram.toCombMap.alpha s ∈ K.walk := by
  obtain ⟨s, hs, hsface, hsin⟩ := PocketWalkColour.exists_sourceDart S hx
  have hinv : S.diagram.toCombMap.alpha s ∈ invDarts S.diagram K.sourceArc.darts := by
    rw [hsrc]
    exact List.mem_map.mpr
      ⟨s, List.mem_reverse.mpr (List.mem_append_left _ (List.mem_append_left _ hs)), rfl⟩
  refine ⟨s, hsface, hsin, ?_⟩
  show _ ∈ K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
    K.targetArc.darts
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv))

/-- **The target split.**  The target arc of the pocket walk lists the target arc of `x` and then a
nonempty proper arc `β` of `∂X` inside the section. -/
theorem exists_target_split (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram} (hxS : x ∈ S.family)
    (hyS : y ∈ S.family) (hxy : x ≠ y) (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length) :
    ∃ β : CyclicArc (outerDarts S.diagram), K.targetArc.darts = x.2.targetArc.darts ++ β.darts ∧
      0 < β.length ∧ β.length < (outerDarts S.diagram).length ∧
        cuts.cut j.castSucc ≤ β.start.1 ∧ β.start.1 + β.length ≤ cuts.cut j.succ := by
  have hx1 := hjx.2.2
  have hnx := (S.nondegenerate x hxS).2
  have hny := (S.nondegenerate y hyS).2
  have hcut := PocketWalk.cut_le_length_outerDarts S j.succ
  have hKle := K.targetArc.length_le
  have hKpos := K.targetArc_pos
  have hKlo := K.lo_le
  have hKhi := K.le_hi
  have hlt : x.2.targetArc.start.1 + x.2.targetArc.length ≤ y.2.targetArc.start.1 := by
    by_cases hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1
    · exact S.targetArc_end_le_start hxS hyS hxy hjx hjy hle
    · have h2 := S.targetArc_end_le_start hyS hxS hxy.symm hjy hjx (by omega)
      omega
  have hT := CyclicArc.exists_transport (targetDarts S.diagram) hjx.1 x.2.targetArc
  obtain ⟨T, hTs, hTl, hTd⟩ : ∃ T : CyclicArc (outerDarts S.diagram),
      T.start.1 = x.2.targetArc.start.1 ∧ T.length = x.2.targetArc.length ∧
        T.darts = x.2.targetArc.darts := hT
  have hpre := darts_eq_append_drop K.targetArc T (by rw [hTs, hstart]) (by omega)
  obtain ⟨β, hβl, hβd, hβs⟩ := exists_suffixArc K.targetArc T.length (by omega)
  have hβs' : β.start.1 = K.targetArc.start.1 + T.length := hβs (by omega)
  refine ⟨β, ?_, by omega, by omega, by omega, by omega⟩
  rw [hβd, ← hTd]
  exact hpre

/-- **The two-arc face set from the pocket.**  Cutting the region `x` off the pocket face set `P`
of the walk `l_y t_1⁻¹ r_x t_2` leaves a face set in walk order with both arcs proper. -/
theorem exists_twoArc_of_pocket (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlea : S.diagram.LeastArea) {i : Fin S.diagram.rCellCount} {j : Fin cuts.count}
    {x y : RegionCandidate D eps S.diagram} (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ)) (hKi : K.source = i)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length) (hc' : K.CopyClean y x)
    (P : PocketFaceSet D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hPw : P.boundary.cycle = K.walk) (hP : P.ClosedWalk) :
    ∃ K' : PocketFaceSet D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
      K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts S.diagram K'.source).length ∧
        K'.targetArc.length < (outerDarts S.diagram).length := by
  obtain ⟨hxS, -, hxt⟩ := PocketWalkColour.mem_exteriorAt S hx
  have hyS := (PocketWalkColour.mem_exteriorAt S hy).1
  have hdisj : Disjoint x.1 y.1 := S.pairwise x hxS y hyS hxy
  obtain ⟨Gap, hsrc⟩ := hgap
  have hxne : x.2.sourceArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [CyclicArc.darts_length]; exact (S.nondegenerate x hxS).1)
  obtain ⟨σ, hσd, hσl⟩ := exists_source_split K hxne (by rw [hsrc, List.append_assoc])
  obtain ⟨β, htgt, hβpos, hβl, hβlo, hβhi⟩ := exists_target_split S hxS hyS hxy hjx hjy K hstart hend
  obtain ⟨s, hsface, hsin, hswalk⟩ := exists_sourceDart_walk S hx K Gap hsrc
  have hsub := region_subset_pocket K P hPw (walk_off_region S hx hdisj K hKi hfirst hsecond)
    hsin hswalk
  have hsrcN : (cell S.diagram K.source).face ∉ P.faces := by
    rw [hKi, ← hsface]
    exact cell_not_mem_pocket P (by rw [hPw]; exact hswalk)
  have hsplit := walk_eq_split K hfirst hsecond Gap β hsrc htgt
  have hMid : invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _
      (List.ne_nil_of_length_pos (by rw [CyclicArc.darts_length]; exact (S.nondegenerate x hxS).2))
  have hβne : β.darts ≠ [] := List.ne_nil_of_length_pos (by rw [CyclicArc.darts_length]; exact hβpos)
  obtain ⟨Bc, hBc⟩ := exists_cut_of_split P.boundary hPw hsplit (region_mem_iff x hxt)
    x.2.leftSide_nodup hsub (leftSide_not_mem_walk K hxt hdisj hfirst hsecond hc') hβne
  have hPp := exists_dartPath_of_closedWalk P hP
  rw [hPw, hsplit] at hPp
  have hclosed := closed_cut hPp (region_dartPath x hxt) hMid
  rw [← hBc] at hclosed
  exact pocket_of_cut P Bc K.source σ β y.2.leftSide (invDarts S.diagram x.2.leftSide)
    (by simp only [hBc, hσd, invDarts]) hclosed hsrcN
    ((x.2.innerGRegion hlea).cells_avoid _ (cell_mem S.diagram P.kept)) y.2.leftSide_length_le
    (by rw [length_invDarts]; exact x.2.leftSide_length_le) y.2.leftSide_norm_le
    (by rw [wordNorm_invDarts]; exact x.2.leftSide_norm_le) hβlo hβhi hσl hβl

end Section

/-- **The two-arc face set producer on a whole section**, on the copy of
`PocketFaceSetOnCopy.exists_copyClean`. -/
theorem input {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ)
    (eps : ℕ) (W : Set (List (RelLetter G Lambda))) :
    SectionPocketFaceSetWholeSectionTwoArcInput.{u, w, v} D lambda c eps W := by
  unfold SectionPocketFaceSetWholeSectionTwoArcInput
  intro Delta cuts hlea S i j a ha b hb hab hja hjb _
  have haS : a ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hbS : b ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hlen0 := PocketFaceSetOnCopy.one_lt_boundaryWord_length S haS hbS hab hja.1 hjb.1
  obtain ⟨S₄, e, ⟨E⟩, hp, hcl⟩ :=
    PocketFaceSetOnCopy.exists_copyClean RegionPairThickening.sectionPocketRegionsCopy hlea S hlen0
  obtain ⟨i', a', b', -, ha', hb', hab', hja', hjb'⟩ :=
    RegionProfileTransport.exists_exteriorPair e hp ha hb hab hja hjb
  have hlea₄ : S₄.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S₄.equiv hlea
  obtain ⟨K, x, y, hxy, hKi, hfirst, hsecond, hgap, hstart, hend, himp⟩ :=
    PocketWalk.exists_pocketFaceSet_of_exteriorAt S₄.toRealizedSectionFamily ha' hb' hab' hja' hjb'
  obtain ⟨hx, hy, hxy', hjx, hjy⟩ : x ∈ RegionCandidate.exteriorAt S₄.family i' ∧
      y ∈ RegionCandidate.exteriorAt S₄.family i' ∧ x ≠ y ∧
        RegionCandidate.TargetsSectionIndex cuts j x ∧
          RegionCandidate.TargetsSectionIndex cuts j y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha', hb', hab', hja', hjb'⟩
    · exact ⟨hb', ha', hab'.symm, hjb', hja'⟩
  have hc : K.CopyClean x y := hcl i' x y hx hy hxy' _ _ K hKi
  have hc' : K.CopyClean y x := hcl i' y x hy hx hxy'.symm _ _ K hKi
  obtain ⟨kept, hkept⟩ := sectionPocketKeptCell D lambda c eps W Delta cuts S₄ hlea₄ i' j x y hx hy
    hxy' hjx hjy K hKi hfirst hsecond hgap hstart hend hc
  obtain ⟨P, hPw, hP⟩ := himp hlea₄ hc ⟨kept, hkept⟩
  exact ⟨S₄.diagram, ⟨E⟩, S₄.label_admissible,
    exists_twoArc_of_pocket S₄.toRealizedSectionFamily hlea₄ hx hy hxy' hjx hjy K hKi hfirst
      hsecond hgap hstart hend hc' P hPw hP⟩

/-- **`OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`**, with `ε₀ = 0` and `ρ₀ = 1`. -/
theorem proof : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v} := by
  unfold OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement
  intro G _ Lambda D _ lambda c _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ W _ => input D lambda c eps W⟩⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.closedWalk_of_closedPath
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.cell_not_mem_pocket
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.pocket_of_cut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.exists_source_split
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.walk_eq_split
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.leftSide_not_mem_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.region_subset_pocket
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.walk_off_region
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.exists_sourceDart_walk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.exists_target_split
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.exists_twoArc_of_pocket
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.input
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece09.proof
