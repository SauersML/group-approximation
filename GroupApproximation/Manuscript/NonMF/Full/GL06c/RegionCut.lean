import GroupApproximation.Manuscript.NonMF.Full.GL06c.RegionArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.Meta.AxiomGuard

/-!
# Cutting the first region off a pocket face set

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), and `thm:hull` (non_mf_groups_exist.tex,
"Hull's small cancellation theorem", ~2121).  Two exterior regions `x`, `y` of the cell `Π` to one
section `q` bound, with `Π` and `q`, a face set `Γ_1` whose boundary is the pocket walk
`s_1 t_1 s_2 t_2`: here `s_1` is the left side of `y`, `t_1 ⊂ ∂Π` runs from the source arc of `x`
over a gap to the source arc of `y`, `s_2` is the right side of `x`, and `t_2 ⊂ q` runs from the
target arc of `x` to the end of the target arc of `y`.

Removing the faces of `x` from `Γ_1` leaves a face set whose boundary is again a pocket walk: the
left side of `y`, the rest of `t_1` after the source arc of `x`, the left side of `x` read
backwards, and the rest of `t_2` after the target arc of `x`.  Both arcs are now proper arcs of
`∂Π` and of `∂Δ`, since each misses the arc of `x`.

* `exists_cut_pocketFaceSet`: the cut pocket face set is a closed walk whose arcs are shorter than
  their carriers.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex) through Osin's Lemma 9.7(b); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06c

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The pocket face set with the first region cut off** (`thm:hull`, Osin Lemma 9.7(b)).  Let
`P` be a pocket face set bounded by the pocket walk `K` of two distinct exterior regions `x`, `y`
of the cell `i` to section `j`, where the source arc of `K` is the source arc of `x`, a gap and
the source arc of `y`, and the target arc of `K` runs from the start of the target arc of `x` to
the end of the target arc of `y`.  Then `P` minus the faces of `x` is a pocket face set of the
same section, a closed walk, whose source and target arcs are shorter than their carriers. -/
theorem exists_cut_pocketFaceSet (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlea : S.diagram.LeastArea) {i : Fin S.diagram.rCellCount} {j : Fin cuts.count}
    {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hKi : K.source = i) (hfirst : K.firstSide = y.2.leftSide)
    (hsecond : K.secondSide = x.2.rightSide)
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (hcyx : K.CopyClean y x)
    (P : PocketFaceSet D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hPc : P.boundary.cycle = K.walk) (hP : P.ClosedWalk) :
    ∃ K' : PocketFaceSet D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
      K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts S.diagram K'.source).length ∧
        K'.targetArc.length < (outerDarts S.diagram).length := by
  classical
  -- The two regions.
  obtain ⟨hxS, -, hxt⟩ := PocketWalkColour.mem_exteriorAt S hx
  obtain ⟨hyS, -, -⟩ := PocketWalkColour.mem_exteriorAt S hy
  have hdisj : Disjoint x.1 y.1 := S.pairwise x hxS y hyS hxy
  obtain ⟨hxs0, hxt0⟩ := S.nondegenerate x hxS
  obtain ⟨hys0, hyt0⟩ := S.nondegenerate y hyS
  have hPx := PocketWalkColour.cell_face_not_mem S hx
  -- The target arc of `x` comes first on the section.
  have hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1 := by
    by_contra hne
    have hyx := RealizedSectionFamily.targetArc_end_le_start S hyS hxS hxy.symm hjy hjx
      (not_le.mp hne).le
    have hKpos := K.targetArc_pos
    omega
  have hxe := RealizedSectionFamily.targetArc_end_le_start S hxS hyS hxy hjx hjy hle
  -- The rest `β` of the target arc of `K` after the target arc of `x`.
  obtain ⟨t, hts, htl, htd⟩ : ∃ t : CyclicArc (outerDarts S.diagram),
      t.start.1 = x.2.targetArc.start.1 ∧ t.length = x.2.targetArc.length ∧
        t.darts = x.2.targetArc.darts :=
    CyclicArc.exists_transport (targetDarts S.diagram) hxt x.2.targetArc
  obtain ⟨β, hβd, hβs, hβl⟩ :=
    exists_suffixArc K.targetArc t (hts.trans hstart.symm) (by omega)
  have hKtgt : K.targetArc.darts = x.2.targetArc.darts ++ β.darts := by
    rw [hβd, htd]
  -- The rest `sArc` of the source arc of `K` after the source arc of `x`.
  obtain ⟨Gap, hsrc⟩ := hgap
  obtain ⟨sArc, hsd, hsl⟩ := exists_dropArc K.sourceArc x.2.sourceArc.darts
    (Gap.darts ++ y.2.sourceArc.darts) (by rw [hsrc, List.append_assoc])
  have hKsrc : K.sourceArc.darts = x.2.sourceArc.darts ++ sArc.darts := by
    rw [hsd, hsrc, List.append_assoc]
  -- The boundary cycle of `x` and the pocket walk, split at the arcs of `x`.
  have hrev : x.2.sourceArc.reverseDarts = invDarts S.diagram x.2.sourceArc.darts := rfl
  have hxcyc : x.2.boundary.cycle = invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++
      x.2.targetArc.darts ++ x.2.leftSide := by
    rw [x.2.boundary_decomposition, hrev,
      targetBoundaryDarts_of_eq_none S.diagram hxt x.2.targetArc]
  have hwalk : K.walk = (y.2.leftSide ++ invDarts S.diagram sArc.darts) ++
      (invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts) ++
        β.darts := by
    show K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts = _
    rw [hfirst, hsecond, hKsrc, hKtgt]
    simp only [invDarts, List.reverse_append, List.map_append, List.append_assoc]
  -- The darts of the pocket walk are the boundary darts of `P`.
  have hbd : ∀ e, e ∈ K.walk ↔ (S.diagram.toCombMap.faceOf e ∈ P.faces ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ P.faces) := by
    intro e
    rw [← hPc]
    exact P.boundary.cycle_mem_iff e
  -- The faces of `x` lie in `P`: `x` is connected and meets `P` across its source arc.
  have hcol : ∀ d, ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ P.faces ↔
      S.diagram.toCombMap.faceOf d ∈ P.faces) ↔
        SimpleClosedWalkSides.walkKeep S.diagram.toCombMap K.walk d := by
    intro d
    have h1 := hbd d
    have h2 := hbd (S.diagram.toCombMap.alpha d)
    rw [S.diagram.toCombMap.alpha_involutive d] at h2
    show _ ↔ (d ∈ K.walk ∨ S.diagram.toCombMap.alpha d ∈ K.walk)
    rw [h1, h2]
    tauto
  have hoffx : ∀ e ∈ K.walk, S.diagram.toCombMap.faceOf e ∈ x.1 →
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha e) ∉ x.1 := by
    intro e he hex
    rcases PocketWalkColour.walk_cases K hKi hfirst hsecond he with h | h | h | h
    · exact h.2
    · exact absurd h.1 (Finset.disjoint_left.mp hdisj hex)
    · rw [h]
      exact hPx
    · rw [h]
      exact fun hmem => (x.2.boundary.all_gCells _ hmem).1 rfl
  obtain ⟨sx, hsx, -, hsxin⟩ := PocketWalkColour.exists_sourceDart S hx
  have hsK : sx ∈ K.sourceArc.darts := by
    rw [hKsrc]
    exact List.mem_append_left _ hsx
  have hinv : S.diagram.toCombMap.alpha sx ∈ invDarts S.diagram K.sourceArc.darts :=
    List.mem_map_of_mem (List.mem_reverse.mpr hsK)
  have hsxw : S.diagram.toCombMap.alpha sx ∈ K.walk := by
    show _ ∈ K.firstSide ++ invDarts S.diagram K.sourceArc.darts ++ K.secondSide ++
      K.targetArc.darts
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv))
  have hsxP := ((hbd _).mp hsxw).1
  have hRP : x.1 ⊆ P.faces := by
    intro f hf
    exact (PocketWalkColour.mem_iff_of_faceSetBoundary hcol x.2.boundary hoffx hf hsxin).mpr
      hsxP
  -- The list hypotheses of the cut.
  have hP' : ∀ d, d ∈ (y.2.leftSide ++ invDarts S.diagram sArc.darts) ++
      (invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts) ++
        β.darts ↔ (S.diagram.toCombMap.faceOf d ∈ P.faces ∧
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∉ P.faces) := by
    intro d
    have h := hbd d
    rwa [hwalk] at h
  have hR : ∀ d, d ∈ (invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++
      x.2.targetArc.darts) ++ x.2.leftSide ↔ (S.diagram.toCombMap.faceOf d ∈ x.1 ∧
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∉ x.1) := by
    intro d
    have h := x.2.boundary.cycle_mem_iff d
    rwa [hxcyc] at h
  have hnodup : ((y.2.leftSide ++ invDarts S.diagram sArc.darts) ++
      (invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts) ++
        β.darts).Nodup := by
    have h := P.boundary.cycle_nodup
    rwa [hPc, hwalk] at h
  have hRnodup : ((invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++
      x.2.targetArc.darts) ++ x.2.leftSide).Nodup := by
    have h := x.2.boundary.cycle_nodup
    rwa [hxcyc] at h
  have hL : ∀ e ∈ x.2.leftSide, e ∉ (y.2.leftSide ++ invDarts S.diagram sArc.darts) ++
      (invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++ x.2.targetArc.darts) ++
        β.darts := by
    intro e he hw
    have hw' : e ∈ K.walk := by
      rw [hwalk]
      exact hw
    have hef := (PocketWalk.mem_leftSide_boundary x he).1
    rcases PocketWalk.mem_walk_cases K hw' with h | h | h | h
    · rw [hfirst] at h
      exact Finset.disjoint_left.mp hdisj hef (PocketWalk.mem_leftSide_boundary y h).1
    · exact hcyx.side_cell e (List.mem_append_left _ he)
        (PocketWalk.faceOf_alpha_of_mem_invDarts_sourceArc K h)
    · rw [hsecond] at h
      exact (List.nodup_append.mp hRnodup).2.2 e
        (List.mem_append_left _ (List.mem_append_right _ h)) e he rfl
    · exact hcyx.side_outer e (List.mem_append_left _ he)
        (PocketWalk.faceOf_alpha_of_mem_targetArc K h)
  -- The kept cell of `P` is not a face of `x`, which is a G-region at least area.
  have hkept : (cell S.diagram P.kept).face ∈ P.faces \ x.1 := by
    exact Finset.mem_sdiff.mpr
      ⟨P.kept_mem, (x.2.innerGRegion hlea).cells_avoid _ (cell_mem S.diagram P.kept)⟩
  -- Lengths and positions of the new arcs.
  rw [List.length_append, y.2.sourceArc.darts_length] at hsl
  have hKl := congrArg List.length hKsrc
  rw [List.length_append, K.sourceArc.darts_length, x.2.sourceArc.darts_length,
    sArc.darts_length] at hKl
  have hKsl := K.sourceArc.length_le
  have hn := PocketWalk.cut_le_length_outerDarts S j.succ
  obtain ⟨-, hjxlo, -⟩ := hjx
  obtain ⟨-, -, hjyhi⟩ := hjy
  have hβs' : β.start.1 = K.targetArc.start.1 + t.length :=
    hβs.trans (Nat.mod_eq_of_lt (by omega))
  have hsArcpos : 0 < sArc.length := by omega
  have hβpos : 0 < β.length := by omega
  have hlo : cuts.cut j.castSucc ≤ β.start.1 := by omega
  have hhi : β.start.1 + β.length ≤ cuts.cut j.succ := by omega
  have hsArcne : sArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [sArc.darts_length]; exact hsArcpos)
  have hβne : β.darts ≠ [] := List.ne_nil_of_length_pos (by rw [β.darts_length]; exact hβpos)
  have hxtne : x.2.targetArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [x.2.targetArc.darts_length]; exact hxt0)
  have hA : y.2.leftSide ++ invDarts S.diagram sArc.darts ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ (invDarts_ne_nil (X := S.diagram) hsArcne)
  have hMid : invDarts S.diagram x.2.sourceArc.darts ++ x.2.rightSide ++
      x.2.targetArc.darts ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ hxtne
  -- The cut walk is closed.
  obtain ⟨hP1, hP2⟩ := hP
  have hP2' := cut_closes_of_last_head (R := fun d e =>
    S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e)
    P.boundary.cycle_nonempty hP2
  rw [hPc, hwalk] at hP1 hP2'
  obtain ⟨hx1, hx2⟩ := x.2.boundary.isChain_closes
  rw [hxcyc] at hx1 hx2
  obtain ⟨hc1, hc2⟩ := isChain_closes_cut hA hMid hβne hP1 hP2' hx1 hx2
  refine ⟨PocketFaceSet.ofBoundaryCycle (cutBoundary hβne hP' hR hRP hnodup hRnodup hL)
    K.source P.kept sArc β y.2.leftSide (invDarts S.diagram x.2.leftSide) rfl hsArcpos hβpos
    hkept y.2.leftSide_length_le
    (by simp only [invDarts, List.length_map, List.length_reverse]; exact x.2.leftSide_length_le)
    y.2.leftSide_norm_le
    (by
      rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
      exact x.2.leftSide_norm_le)
    hlo hhi, ?_, ?_, ?_⟩
  · exact ⟨hc1, cut_last_head_of_closes (R := fun d e =>
      S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha d) =
        S.diagram.toCombMap.vertexOf e) (List.append_ne_nil_of_right_ne_nil _ hβne) hc2⟩
  · show sArc.length < (cellDarts S.diagram K.source).length
    omega
  · show β.length < (outerDarts S.diagram).length
    omega

end GroupApproximation.Full.GL06c

#audit_axioms GroupApproximation.Full.GL06c.exists_cut_pocketFaceSet
