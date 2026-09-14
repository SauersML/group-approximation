import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonClassHyp
import GroupApproximation.Meta.AxiomGuard

/-!
# The faces of a two-gon pocket without a connected walk

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  debt-conditional's
`ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon` (`hno`) and
`ExtPhiData.disjoint_sideFaces_of_twoGon` (`havoid`) show that the side of a pocket walk holds no
relator cell and meets no region other than `a` and `b`.  They take `TwoGonWalkHyp`, whose field
`connected` asks that all darts of the walk lie in one face class of the walk.  That fails when
the walk touches itself at a pinch (`OsinPocketMixedTouchModel`, Configuration A), and a pocket
walk kept only through Euler equalities (`TwoGonEulerWalkInput`) can touch itself there.

Crossing an edge off the walk keeps a side face a face of the pocket using only the side, outer
and cell fields of the walk hypotheses.  So `connected` and `base` can be traded for one condition:
every dart of the walk lies on a face of the pocket.

* `TwoGonWalkSideHyp`: the fields `left_side`, `right_side`, `outer_off` and `cell_off` of
  `TwoGonWalkHyp`, with `TwoGonWalkHyp.toSideHyp`.
* `ExtPhiData.twoGonPocketFace_alpha_of_sideHyp`, `ExtPhiData.twoGonPocketFace_iff_of_eqvGen_of_sideHyp`:
  the transport along face classes of the walk.
* `ExtPhiData.twoGonPocketFace_of_mem_sideFaces_of_base`: every side face is a face of the pocket,
  once every walk dart is.
* `ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon_of_base`,
  `ExtPhiData.disjoint_sideFaces_of_twoGon_of_base`: `hno` and `havoid` from it.
* `twoGonPocketFace_of_mem_decomposition`: on the walk
  `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide`, the darts of the sides of `a`
  and `b` and those across their arcs lie on faces of `a` or `b`, so the condition is needed only
  for the darts of the spans outside the arcs of `a` and `b`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open SimpleClosedWalkSides

namespace Embedded.RegionCandidate

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

/-- **The side hypotheses on a closed walk around the pocket** between `a` and `b`: the boundary
darts of `a` off the walk lie on its left side and those of `b` on its right side, and the outer
face and cell `i` are off the side of the walk. -/
structure TwoGonWalkSideHyp (a b : RegionCandidate D eps Delta) (i : Fin Delta.rCellCount)
    (walk : List Delta.toCombMap.Dart) : Prop where
  left_side : ∀ d ∈ a.2.boundary.cycle, ¬ walkKeep Delta.toCombMap walk d → d ∈ a.2.leftSide
  right_side : ∀ d ∈ b.2.boundary.cycle, ¬ walkKeep Delta.toCombMap walk d → d ∈ b.2.rightSide
  outer_off : Delta.outerFace ∉ sideFaces Delta.toCombMap walk
  cell_off : (cell Delta i).face ∉ sideFaces Delta.toCombMap walk

variable {x : (collapsedMap family).Dart} {a b : RegionCandidate D eps Delta}
  {i : Fin Delta.rCellCount} {walk : List Delta.toCombMap.Dart}

theorem TwoGonWalkHyp.toSideHyp (Hw : TwoGonWalkHyp a b i walk) :
    TwoGonWalkSideHyp a b i walk :=
  ⟨Hw.left_side, Hw.right_side, Hw.outer_off, Hw.cell_off⟩

/-- **Crossing an edge off the walk keeps a side face a face of the pocket**, from the side
hypotheses alone. -/
theorem ExtPhiData.twoGonPocketFace_alpha_of_sideHyp (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hs : TwoGonWalkSideHyp a b i walk)
    {z : Delta.toCombMap.Dart} (hk : ¬ walkKeep Delta.toCombMap walk z)
    (hzs : Delta.toCombMap.faceOf z ∈ sideFaces Delta.toCombMap walk)
    (hαs : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ∈ sideFaces Delta.toCombMap walk)
    (hF : TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf z)) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf (Delta.toCombMap.alpha z)) := by
  have hαout : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ Delta.outerFace :=
    fun h => Hs.outer_off (by rw [← h]; exact hαs)
  have hαcell : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ (cell Delta i).face :=
    fun h => Hs.cell_off (by rw [← h]; exact hαs)
  have hcross : ∀ hz₀ : ¬ RegionInternal family z, FaceClassO family E x ⟨z, hz₀⟩ →
      ¬ PhiKeepO family E ⟨z, hz₀⟩ →
      TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf (Delta.toCombMap.alpha z)) := by
    intro hz₀ hxz hkz
    have hZ : FaceClassO family E x ((collapsedMap family).alpha ⟨z, hz₀⟩) :=
      Relation.EqvGen.trans _ _ _ hxz (Relation.EqvGen.rel _ _ (Or.inr ⟨hkz, rfl⟩))
    have hval : ((collapsedMap family).alpha ⟨z, hz₀⟩).1 = Delta.toCombMap.alpha z :=
      (collapsedMap_isRestriction family).alpha_map ⟨z, hz₀⟩
    have h := P.twoGonPocketFace_of_faceClassO H.mem_left H.mem_right i H.kept_faces
      H.selected_of_source H.nondegenerate hZ (by rw [hval]; exact hαout)
      (by rw [hval]; exact hαcell)
    rwa [hval] at h
  unfold TwoGonPocketFace at hF
  rcases hF with hFa | hFb | ⟨hF, hFx⟩
  · by_cases hαa : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ∈ a.1
    · exact Or.inl hαa
    have hcyc : z ∈ a.2.boundary.cycle := (a.2.boundary.cycle_mem_iff z).mpr ⟨hFa, hαa⟩
    have hz₀ := not_regionInternal_of_mem_cycle P.pairwise H.mem_left hcyc
    obtain ⟨u₀, hu₀, hZ₀⟩ := H.start_left
    obtain ⟨hxz, hkz⟩ := P.faceClassO_of_mem_leftSide H.mem_left H.target_left hu₀ hZ₀ z
      (Hs.left_side z hcyc hk) hz₀
    exact hcross hz₀ hxz hkz
  · by_cases hαb : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ∈ b.1
    · exact Or.inr (Or.inl hαb)
    have hcyc : z ∈ b.2.boundary.cycle := (b.2.boundary.cycle_mem_iff z).mpr ⟨hFb, hαb⟩
    have hz₀ := not_regionInternal_of_mem_cycle P.pairwise H.mem_right hcyc
    obtain ⟨u₁, hu₁, hZ₁⟩ := H.start_right
    obtain ⟨hxz, hkz⟩ := P.faceClassO_of_mem_rightSide H.mem_right H.target_right hu₁ hZ₁ z
      (Hs.right_side z hcyc hk) hz₀
    exact hcross hz₀ hxz hkz
  · have hz₀ : ¬ RegionInternal family z := not_regionInternal_of_face_not_mem hF
    have hxz := hFx ⟨z, hz₀⟩ rfl
    refine hcross hz₀ hxz fun hkz => ?_
    rcases H.kept_faces _ hxz hkz with h | h | h | h
    · exact Hs.outer_off (by rw [← h]; exact hzs)
    · exact hF a H.mem_left h
    · exact Hs.cell_off (by rw [← h]; exact hzs)
    · exact hF b H.mem_right h

/-- **Faces of the pocket along a face class of the walk**, from the side hypotheses alone. -/
theorem ExtPhiData.twoGonPocketFace_iff_of_eqvGen_of_sideHyp (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hs : TwoGonWalkSideHyp a b i walk)
    {z z' : Delta.toCombMap.Dart} (h : Relation.EqvGen
      (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap walk)) z z') :
    Delta.toCombMap.faceOf z ∈ sideFaces Delta.toCombMap walk →
      (TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf z) ↔
        TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf z')) := by
  have hside : ∀ z₁ z₂, Relation.EqvGen
      (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap walk)) z₁ z₂ →
      Delta.toCombMap.faceOf z₁ ∈ sideFaces Delta.toCombMap walk →
      Delta.toCombMap.faceOf z₂ ∈ sideFaces Delta.toCombMap walk := by
    intro z₁ z₂ h₁₂ hs
    obtain ⟨d, hd, hdz⟩ := (mem_sideFaces_iff _ _ z₁).mp hs
    exact (mem_sideFaces_iff _ _ z₂).mpr ⟨d, hd, .trans _ _ _ hdz h₁₂⟩
  induction h with
  | rel z₁ z₂ hstep =>
      intro hs
      rcases hstep with rfl | ⟨hkz, rfl⟩
      · rw [Delta.toCombMap.faceOf_facePerm]
      · have hαs := hside z₁ (Delta.toCombMap.alpha z₁) (.rel _ _ (Or.inr ⟨hkz, rfl⟩)) hs
        refine ⟨P.twoGonPocketFace_alpha_of_sideHyp H Hs hkz hs hαs, fun hF => ?_⟩
        have hkα : ¬ walkKeep Delta.toCombMap walk (Delta.toCombMap.alpha z₁) := by
          rwa [walkKeep_alpha]
        have h' := P.twoGonPocketFace_alpha_of_sideHyp H Hs hkα hαs
          (by rw [Delta.toCombMap.alpha_involutive z₁]; exact hs) hF
        rwa [Delta.toCombMap.alpha_involutive z₁] at h'
  | refl => intro _; exact Iff.rfl
  | symm z₁ z₂ h₁₂ ih => intro hs; exact (ih (hside z₂ z₁ (.symm _ _ h₁₂) hs)).symm
  | trans z₁ z₂ z₃ h₁₂ _ ih₁ ih₂ => intro hs; exact (ih₁ hs).trans (ih₂ (hside z₁ z₂ h₁₂ hs))

/-- **Every face on the side of the walk is a face of the pocket**, once every walk dart lies on a
face of the pocket: a side face is in the face class of the walk of some walk dart. -/
theorem ExtPhiData.twoGonPocketFace_of_mem_sideFaces_of_base (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hs : TwoGonWalkSideHyp a b i walk)
    (hbase : ∀ d ∈ walk, TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d))
    {F : Delta.toCombMap.Face} (hF : F ∈ sideFaces Delta.toCombMap walk) :
    TwoGonPocketFace family E x a b F := by
  obtain ⟨z, hz⟩ := Quotient.exists_rep F
  have hz' : Delta.toCombMap.faceOf z = F := hz
  subst hz'
  obtain ⟨d, hd, hdz⟩ := (mem_sideFaces_iff _ _ z).mp hF
  have hs : Delta.toCombMap.faceOf d ∈ sideFaces Delta.toCombMap walk :=
    (mem_sideFaces_iff _ _ d).mpr ⟨d, hd, .refl _⟩
  exact (P.twoGonPocketFace_iff_of_eqvGen_of_sideHyp H Hs hdz hs).mp (hbase d hd)

/-- **No relator cell lies on the side of the walk** (`hno`), without `connected`. -/
theorem ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon_of_base (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hs : TwoGonWalkSideHyp a b i walk)
    (hbase : ∀ d ∈ walk, TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d))
    (hend : ∀ (k : Fin Delta.rCellCount) (v : (collapsedMap family).Dart),
      FaceClassO family E x v → Delta.toCombMap.faceOf v.1 = (cell Delta k).face →
        some k ∈ endCellsO E)
    (k : Fin Delta.rCellCount) : (cell Delta k).face ∉ sideFaces Delta.toCombMap walk := by
  intro hk
  have hF := P.twoGonPocketFace_of_mem_sideFaces_of_base H Hs hbase hk
  unfold TwoGonPocketFace at hF
  rcases hF with h | h | ⟨hF, hFx⟩
  · exact P.cell_not_mem a H.mem_left k h
  · exact P.cell_not_mem b H.mem_right k h
  obtain ⟨z, hz⟩ := Quotient.exists_rep (cell Delta k).face
  have hz' : Delta.toCombMap.faceOf z = (cell Delta k).face := hz
  have hz₀ : ¬ RegionInternal family z :=
    not_regionInternal_of_face_not_mem fun r hr h => hF r hr (by rw [← hz']; exact h)
  obtain ⟨r, hrE, s, hrs⟩ := mem_endCellsO.mp (hend k ⟨z, hz₀⟩ (hFx ⟨z, hz₀⟩ hz') hz')
  obtain ⟨p, hp⟩ := exists_crossO r (H.nondegenerate r (P.subset hrE)) s true
  have hpface : Delta.toCombMap.faceOf p = (cell Delta k).face := by
    have h := faceOf_crossO_true r hp
    rw [hrs] at h
    exact h
  have hp₀ : ¬ RegionInternal family p :=
    not_regionInternal_of_face_not_mem fun r hr h => hF r hr (by rw [← hpface]; exact h)
  rcases H.kept_faces ⟨p, hp₀⟩ (hFx ⟨p, hp₀⟩ hpface) ⟨r, hrE, s, true, hp⟩ with h | h | h | h
  · exact (cell Delta k).face_ne_outer (hpface.symm.trans h)
  · exact P.cell_not_mem a H.mem_left k (by rw [← hpface]; exact h)
  · exact Hs.cell_off (by rw [← cell_face_injective Delta (hpface.symm.trans h)]; exact hk)
  · exact P.cell_not_mem b H.mem_right k (by rw [← hpface]; exact h)

/-- **No other region meets the side of the walk** (`havoid`), without `connected`. -/
theorem ExtPhiData.disjoint_sideFaces_of_twoGon_of_base (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hs : TwoGonWalkSideHyp a b i walk)
    (hbase : ∀ d ∈ walk, TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d))
    {r : RegionCandidate D eps Delta} (hr : r ∈ family) (hra : r ≠ a) (hrb : r ≠ b) :
    Disjoint r.1 (sideFaces Delta.toCombMap walk) := by
  refine Finset.disjoint_left.mpr fun F hFr hFs => ?_
  have hF := P.twoGonPocketFace_of_mem_sideFaces_of_base H Hs hbase hFs
  unfold TwoGonPocketFace at hF
  rcases hF with h | h | ⟨hF, -⟩
  · exact hra (eq_of_face_mem_of_face_mem P.pairwise hr H.mem_left hFr h)
  · exact hrb (eq_of_face_mem_of_face_mem P.pairwise hr H.mem_right hFr h)
  · exact hF r hr hFr

/-- A dart of the right side of `a` lies on a face of `a`. -/
theorem twoGonPocketFace_of_mem_rightSide {d : Delta.toCombMap.Dart} (hd : d ∈ a.2.rightSide) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d) := by
  have hcyc : d ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr hd))
  exact Or.inl ((a.2.boundary.cycle_mem_iff d).mp hcyc).1

/-- A dart of the left side of `b` lies on a face of `b`. -/
theorem twoGonPocketFace_of_mem_leftSide_right {d : Delta.toCombMap.Dart}
    (hd : d ∈ b.2.leftSide) : TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d) := by
  have hcyc : d ∈ b.2.boundary.cycle := by
    rw [b.2.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inr hd
  exact Or.inr (Or.inl ((b.2.boundary.cycle_mem_iff d).mp hcyc).1)

/-- The dart across a source dart of `a` lies on a face of `a`. -/
theorem twoGonPocketFace_of_alpha_mem_sourceArc_left {p : Delta.toCombMap.Dart}
    (hp : p ∈ a.2.sourceArc.darts) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf (Delta.toCombMap.alpha p)) := by
  have hcyc : Delta.toCombMap.alpha p ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    simp only [List.mem_append]
    refine Or.inl (Or.inl (Or.inl ?_))
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨p, hp, rfl⟩
  exact Or.inl ((a.2.boundary.cycle_mem_iff _).mp hcyc).1

/-- The dart across a source dart of `b` lies on a face of `b`. -/
theorem twoGonPocketFace_of_alpha_mem_sourceArc_right {p : Delta.toCombMap.Dart}
    (hp : p ∈ b.2.sourceArc.darts) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf (Delta.toCombMap.alpha p)) := by
  have hcyc : Delta.toCombMap.alpha p ∈ b.2.boundary.cycle := by
    rw [b.2.boundary_decomposition]
    simp only [List.mem_append]
    refine Or.inl (Or.inl (Or.inl ?_))
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse]
    exact ⟨p, hp, rfl⟩
  exact Or.inr (Or.inl ((b.2.boundary.cycle_mem_iff _).mp hcyc).1)

/-- A target dart of `a`, a region with a boundary target, lies on a face of `a`. -/
theorem twoGonPocketFace_of_mem_targetArc_left (ht : a.2.target = none)
    {d : Delta.toCombMap.Dart} (hd : d ∈ a.2.targetArc.darts) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d) := by
  have hcyc : d ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inl (Or.inr
      (mem_targetBoundaryDarts_of_eq_none Delta a.2.target a.2.targetArc ht hd))
  exact Or.inl ((a.2.boundary.cycle_mem_iff d).mp hcyc).1

/-- A target dart of `b`, a region with a boundary target, lies on a face of `b`. -/
theorem twoGonPocketFace_of_mem_targetArc_right (ht : b.2.target = none)
    {d : Delta.toCombMap.Dart} (hd : d ∈ b.2.targetArc.darts) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d) := by
  have hcyc : d ∈ b.2.boundary.cycle := by
    rw [b.2.boundary_decomposition]
    simp only [List.mem_append]
    exact Or.inl (Or.inr
      (mem_targetBoundaryDarts_of_eq_none Delta b.2.target b.2.targetArc ht hd))
  exact Or.inr (Or.inl ((b.2.boundary.cycle_mem_iff d).mp hcyc).1)

/-- **Every dart of the decomposition walk lies on a face of the pocket**, once the darts of the
spans outside the arcs of `a` and `b` do. -/
theorem twoGonPocketFace_of_mem_decomposition (source : CyclicArc (cellDarts Delta i))
    (target : CyclicArc (targetDarts Delta none)) (hta : a.2.target = none)
    (htb : b.2.target = none)
    (hgapS : ∀ p ∈ source.darts, p ∉ a.2.sourceArc.darts → p ∉ b.2.sourceArc.darts →
      TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf (Delta.toCombMap.alpha p)))
    (hgapT : ∀ d ∈ target.darts, d ∉ a.2.targetArc.darts → d ∉ b.2.targetArc.darts →
      TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d)) :
    ∀ d ∈ source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide,
      TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf d) := by
  classical
  intro d hd
  simp only [List.mem_append] at hd
  rcases hd with ((hs | hr) | htg) | hl
  · simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    by_cases hpa : p ∈ a.2.sourceArc.darts
    · exact twoGonPocketFace_of_alpha_mem_sourceArc_left hpa
    · by_cases hpb : p ∈ b.2.sourceArc.darts
      · exact twoGonPocketFace_of_alpha_mem_sourceArc_right hpb
      · exact hgapS p hp hpa hpb
  · exact twoGonPocketFace_of_mem_rightSide hr
  · by_cases hda : d ∈ a.2.targetArc.darts
    · exact twoGonPocketFace_of_mem_targetArc_left hta hda
    · by_cases hdb : d ∈ b.2.targetArc.darts
      · exact twoGonPocketFace_of_mem_targetArc_right htb hdb
      · exact hgapT d htg hda hdb
  · exact twoGonPocketFace_of_mem_leftSide_right hl

end Embedded.RegionCandidate

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.TwoGonWalkHyp.toSideHyp
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.twoGonPocketFace_alpha_of_sideHyp
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.twoGonPocketFace_iff_of_eqvGen_of_sideHyp
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.twoGonPocketFace_of_mem_sideFaces_of_base
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon_of_base
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.disjoint_sideFaces_of_twoGon_of_base
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.twoGonPocketFace_of_mem_decomposition
