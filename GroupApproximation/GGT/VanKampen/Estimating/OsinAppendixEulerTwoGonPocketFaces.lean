import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonPocketClass
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The faces on the side of a two-gon pocket walk

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  A two-gon of `phiMapO` with no corner
in its gap bounds a pocket between two exterior regions `a` and `b` of one cell `i`, both with
boundary targets.  A closed walk around the pocket, such as the pocket walk `s_1 t_1 s_2 t_2` of
`PocketWalk.exists_of_exteriorAt`, has faces on its side (`SimpleClosedWalkSides.sideFaces`).  This
module shows that they are faces of the pocket (`TwoGonPocketFace`), and derives the premises
`hno` and `havoid` of `exists_kept_of_simple` (`OsinPocketKeptCell`).

* `TwoGonClassHyp`, `TwoGonWalkHyp`: the hypotheses on the face class `x` of the two-gon and on the
  walk.
* `ExtPhiData.twoGonPocketFace_alpha`, `ExtPhiData.twoGonPocketFace_iff_of_eqvGen`: crossing an
  edge off the walk keeps a side face a face of the pocket.
* `ExtPhiData.twoGonPocketFace_of_mem_sideFaces`: every face on the side is a face of the pocket.
* `ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon`: no relator cell lies on the side, when every
  cell met by the class `x` is an end cell of `E` (`hno`).
* `ExtPhiData.disjoint_sideFaces_of_twoGon`: no region other than `a` and `b` meets the side
  (`havoid`).
* `IsSimpleClosedWalk.eqvGen_of_mem`: the darts of a simple closed walk lie in one face class of
  the walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open SimpleClosedWalkSides

namespace IsSimpleClosedWalk

variable {M : CombMap.{u}} {walk : List M.Dart}

/-- A step of a simple closed walk stays in one face class of the walk: the rotation from the
reversal of `a` to the next walk dart `b` passes only darts off the walk. -/
theorem eqvGen_next (hw : IsSimpleClosedWalk M walk) {a b : M.Dart} (ha : a ∈ walk)
    (hb : b ∈ walk) (hab : M.vertexOf (M.alpha a) = M.vertexOf b) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M walk)) a b := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (walkMap_isRestriction M walk).sigma_firstReturn ⟨M.alpha a, hw.alpha_keep ha⟩
  have hpm' : (M.sigma ^ m) (M.alpha a) = b :=
    hpm.trans (congrArg Subtype.val (hw.walkMap_sigma_alpha ha hb hab (hw.alpha_keep ha)))
  rw [← hpm']
  exact faceClass_run M (walkKeep M walk) a m
    (fun k hk0 hkm hkeep => havoid k hk0 hkm ⟨⟨_, hkeep⟩, rfl⟩) m hm le_rfl

/-- The darts of a simple closed walk lie in one face class of the walk. -/
theorem eqvGen_of_mem (hw : IsSimpleClosedWalk M walk) {d e : M.Dart} (hd : d ∈ walk)
    (he : e ∈ walk) : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M walk)) d e := by
  have hhead : ∀ x ∈ walk,
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M walk)) (walk.head hw.ne_nil) x := by
    refine List.IsChain.induction (fun x =>
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M walk)) (walk.head hw.ne_nil) x)
      walk (List.IsChain.iff_mem.mp hw.chain) ?_ ?_
    · rintro x y ⟨hxw, hyw, hxy⟩ h
      exact .trans _ _ _ h (hw.eqvGen_next hxw hyw hxy)
    · intro _
      exact .refl _
  exact .trans _ _ _ (.symm _ _ (hhead d hd)) (hhead e he)

end IsSimpleClosedWalk

namespace Embedded.RegionCandidate

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

/-- **The hypotheses on the face class `x` of a two-gon** with exterior regions `a` and `b` of
cell `i`, both with boundary targets.  The retained darts of the class lie on the outer face, in
`a`, on cell `i` or in `b`; a region whose source cell the class meets is selected; every region
is nondegenerate; and the class holds the reverse of the first target dart of `a` and the first
source dart of `b`. -/
structure TwoGonClassHyp (family E : Finset (RegionCandidate D eps Delta))
    (x : (collapsedMap family).Dart) (a b : RegionCandidate D eps Delta)
    (i : Fin Delta.rCellCount) : Prop where
  mem_left : a ∈ family
  mem_right : b ∈ family
  target_left : a.2.target = none
  target_right : b.2.target = none
  kept_faces : ∀ u, FaceClassO family E x u → PhiKeepO family E u →
    Delta.toCombMap.faceOf u.1 = Delta.outerFace ∨ Delta.toCombMap.faceOf u.1 ∈ a.1 ∨
      Delta.toCombMap.faceOf u.1 = (cell Delta i).face ∨ Delta.toCombMap.faceOf u.1 ∈ b.1
  selected_of_source : ∀ u, FaceClassO family E x u → ∀ r ∈ family,
    Delta.toCombMap.faceOf u.1 = (cell Delta r.2.source).face → r ∈ E
  nondegenerate : ∀ r ∈ family, 0 < r.2.sourceArc.length ∧ 0 < r.2.targetArc.length
  start_left : ∃ u₀ : (collapsedMap family).Dart,
    a.2.targetArc.darts.head? = some (Delta.toCombMap.alpha u₀.1) ∧ FaceClassO family E x u₀
  start_right : ∃ u₁ : (collapsedMap family).Dart,
    b.2.sourceArc.darts.head? = some u₁.1 ∧ FaceClassO family E x u₁

/-- **The hypotheses on a closed walk around the pocket** between `a` and `b`.  The boundary darts
of `a` off the walk lie on its left side and those of `b` on its right side; the outer face and
cell `i` are off the side of the walk; the darts of the walk lie in one face class of the walk;
and one of them lies in `a`. -/
structure TwoGonWalkHyp (a b : RegionCandidate D eps Delta) (i : Fin Delta.rCellCount)
    (walk : List Delta.toCombMap.Dart) : Prop where
  left_side : ∀ d ∈ a.2.boundary.cycle, ¬ walkKeep Delta.toCombMap walk d → d ∈ a.2.leftSide
  right_side : ∀ d ∈ b.2.boundary.cycle, ¬ walkKeep Delta.toCombMap walk d → d ∈ b.2.rightSide
  outer_off : Delta.outerFace ∉ sideFaces Delta.toCombMap walk
  cell_off : (cell Delta i).face ∉ sideFaces Delta.toCombMap walk
  connected : ∀ d ∈ walk, ∀ e ∈ walk,
    Relation.EqvGen (CombMap.FaceClassStep Delta.toCombMap (walkKeep Delta.toCombMap walk)) d e
  base : ∃ d ∈ walk, Delta.toCombMap.faceOf d ∈ a.1

variable {x : (collapsedMap family).Dart} {a b : RegionCandidate D eps Delta}
  {i : Fin Delta.rCellCount} {walk : List Delta.toCombMap.Dart}

/-- **Crossing an edge off the walk keeps a side face a face of the pocket.**  A boundary dart of
`a` or `b` off the walk lies on the left side of `a` or the right side of `b`, in the class `x`
and not retained; a dart of a face outside the regions is in the class, and not retained since its
face is on the side. -/
theorem ExtPhiData.twoGonPocketFace_alpha (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hw : TwoGonWalkHyp a b i walk)
    {z : Delta.toCombMap.Dart} (hk : ¬ walkKeep Delta.toCombMap walk z)
    (hzs : Delta.toCombMap.faceOf z ∈ sideFaces Delta.toCombMap walk)
    (hαs : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ∈ sideFaces Delta.toCombMap walk)
    (hF : TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf z)) :
    TwoGonPocketFace family E x a b (Delta.toCombMap.faceOf (Delta.toCombMap.alpha z)) := by
  have hαout : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ Delta.outerFace :=
    fun h => Hw.outer_off (by rw [← h]; exact hαs)
  have hαcell : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ (cell Delta i).face :=
    fun h => Hw.cell_off (by rw [← h]; exact hαs)
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
      (Hw.left_side z hcyc hk) hz₀
    exact hcross hz₀ hxz hkz
  · by_cases hαb : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ∈ b.1
    · exact Or.inr (Or.inl hαb)
    have hcyc : z ∈ b.2.boundary.cycle := (b.2.boundary.cycle_mem_iff z).mpr ⟨hFb, hαb⟩
    have hz₀ := not_regionInternal_of_mem_cycle P.pairwise H.mem_right hcyc
    obtain ⟨u₁, hu₁, hZ₁⟩ := H.start_right
    obtain ⟨hxz, hkz⟩ := P.faceClassO_of_mem_rightSide H.mem_right H.target_right hu₁ hZ₁ z
      (Hw.right_side z hcyc hk) hz₀
    exact hcross hz₀ hxz hkz
  · have hz₀ : ¬ RegionInternal family z := not_regionInternal_of_face_not_mem hF
    have hxz := hFx ⟨z, hz₀⟩ rfl
    refine hcross hz₀ hxz fun hkz => ?_
    rcases H.kept_faces _ hxz hkz with h | h | h | h
    · exact Hw.outer_off (by rw [← h]; exact hzs)
    · exact hF a H.mem_left h
    · exact Hw.cell_off (by rw [← h]; exact hzs)
    · exact hF b H.mem_right h

/-- **Faces of the pocket along a face class of the walk.**  Two darts in one face class of the
walk, the first on its side, lie on faces of the pocket together. -/
theorem ExtPhiData.twoGonPocketFace_iff_of_eqvGen (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hw : TwoGonWalkHyp a b i walk)
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
        refine ⟨P.twoGonPocketFace_alpha H Hw hkz hs hαs, fun hF => ?_⟩
        have hkα : ¬ walkKeep Delta.toCombMap walk (Delta.toCombMap.alpha z₁) := by
          rwa [walkKeep_alpha]
        have h' := P.twoGonPocketFace_alpha H Hw hkα hαs
          (by rw [Delta.toCombMap.alpha_involutive z₁]; exact hs) hF
        rwa [Delta.toCombMap.alpha_involutive z₁] at h'
  | refl => intro _; exact Iff.rfl
  | symm z₁ z₂ h₁₂ ih => intro hs; exact (ih (hside z₂ z₁ (.symm _ _ h₁₂) hs)).symm
  | trans z₁ z₂ z₃ h₁₂ _ ih₁ ih₂ => intro hs; exact (ih₁ hs).trans (ih₂ (hside z₁ z₂ h₁₂ hs))

/-- **Every face on the side of the walk is a face of the pocket**: it lies in the face class of
the walk of a walk dart in `a`. -/
theorem ExtPhiData.twoGonPocketFace_of_mem_sideFaces (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hw : TwoGonWalkHyp a b i walk)
    {F : Delta.toCombMap.Face} (hF : F ∈ sideFaces Delta.toCombMap walk) :
    TwoGonPocketFace family E x a b F := by
  obtain ⟨z, hz⟩ := Quotient.exists_rep F
  have hz' : Delta.toCombMap.faceOf z = F := hz
  subst hz'
  obtain ⟨d, hd, hdz⟩ := (mem_sideFaces_iff _ _ z).mp hF
  obtain ⟨d₀, hd₀, hd₀a⟩ := Hw.base
  have hs₀ : Delta.toCombMap.faceOf d₀ ∈ sideFaces Delta.toCombMap walk :=
    (mem_sideFaces_iff _ _ d₀).mpr ⟨d₀, hd₀, .refl _⟩
  exact (P.twoGonPocketFace_iff_of_eqvGen H Hw
    (.trans _ _ _ (Hw.connected d₀ hd₀ d hd) hdz) hs₀).mp (Or.inl hd₀a)

/-- **No relator cell lies on the side of the walk** (`hno`), when every cell met by the class `x`
is an end cell of `E`.  A cell on the side is a face of the pocket outside the regions, so the
class holds its darts.  A region of `E` ends at the cell, and its retained crossing dart on the
cell lies in the class, so the cell is cell `i`, which is off the side. -/
theorem ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hw : TwoGonWalkHyp a b i walk)
    (hend : ∀ (k : Fin Delta.rCellCount) (v : (collapsedMap family).Dart),
      FaceClassO family E x v → Delta.toCombMap.faceOf v.1 = (cell Delta k).face →
        some k ∈ endCellsO E)
    (k : Fin Delta.rCellCount) : (cell Delta k).face ∉ sideFaces Delta.toCombMap walk := by
  intro hk
  have hF := P.twoGonPocketFace_of_mem_sideFaces H Hw hk
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
  · exact Hw.cell_off (by rw [← cell_face_injective Delta (hpface.symm.trans h)]; exact hk)
  · exact P.cell_not_mem b H.mem_right k (by rw [← hpface]; exact h)

/-- **No other region meets the side of the walk** (`havoid`): a face of the pocket lies in `a`,
in `b`, or outside the regions. -/
theorem ExtPhiData.disjoint_sideFaces_of_twoGon (P : ExtPhiData family E)
    (H : TwoGonClassHyp family E x a b i) (Hw : TwoGonWalkHyp a b i walk)
    {r : RegionCandidate D eps Delta} (hr : r ∈ family) (hra : r ≠ a) (hrb : r ≠ b) :
    Disjoint r.1 (sideFaces Delta.toCombMap walk) := by
  refine Finset.disjoint_left.mpr fun F hFr hFs => ?_
  have hF := P.twoGonPocketFace_of_mem_sideFaces H Hw hFs
  unfold TwoGonPocketFace at hF
  rcases hF with h | h | ⟨hF, -⟩
  · exact hra (eq_of_face_mem_of_face_mem P.pairwise hr H.mem_left hFr h)
  · exact hrb (eq_of_face_mem_of_face_mem P.pairwise hr H.mem_right hFr h)
  · exact hF r hr hFr

end Embedded.RegionCandidate

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.eqvGen_next
#audit_axioms GroupApproximation.GGT.VanKampen.IsSimpleClosedWalk.eqvGen_of_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.twoGonPocketFace_alpha
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.twoGonPocketFace_iff_of_eqvGen
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.twoGonPocketFace_of_mem_sideFaces
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.disjoint_sideFaces_of_twoGon
