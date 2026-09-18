import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.VertexComplex
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.FrameComplex
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank four: lane 07's frame complex agrees with lane 10's `frameComplexFour`

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Lane `sk-leavitt-10` (`FrameFan.FrameComplex`, on
disk) defines `IsFrameVertex/Edge/Triangle` as "the first `k` columns of a unit of `M_4(A)`" and
builds `frameComplexFour A` on `FrameFan.FrameVertex A`.  Lane 07's frames are "distinct columns
of a unit" (`IsFrame`), equivalently the first `k` columns (`isFrame_iff_firstColumns`).  Here:

* `frameFan_isFrameVertex_iff`, `frameFan_isFrameEdge_iff`, `frameFan_isFrameTriangle_iff`:
  the two notions of frame agree;
* `frameVertexFourEquiv`: the two vertex types are equivalent, compatibly with edges and
  triangles (`frameComplexFour_edge_iff`, `frameComplexFour_tri_iff`);
* `frameFanVertexMulAction` and `frameComplexFour_action`: `GL_4(A)` acts on lane 10's
  complex, preserving ordered edges and ordered triangles.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {n : ℕ}

/-- `g • e_j` is the `j`-th column of `g`. -/
theorem frame_smul_single_apply (g : (Matrix (Fin n) (Fin n) A)ˣ) (j r : Fin n) :
    (g • (Pi.single j 1 : Fin n → A)) r = (g : Matrix (Fin n) (Fin n) A) r j := by
  rw [frame_smul_def, Matrix.mulVec_single_one, Matrix.col_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_smul_single_apply

theorem frameFan_isFrameVertex_iff (u : Fin 4 → A) :
    FrameFan.IsFrameVertex A u ↔ frameVertex u := by
  rw [frameVertex, isFrame_iff_firstColumns (by decide : 1 ≤ 4)]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun i => ?_⟩
    funext r
    rw [frame_smul_single_apply]
    fin_cases i
    exact (hg r).symm
  · rintro ⟨g, hg⟩
    refine ⟨g, fun r => ?_⟩
    have h := congrFun (hg 0) r
    rw [frame_smul_single_apply] at h
    exact h.symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameFan_isFrameVertex_iff

theorem frameFan_isFrameEdge_iff (u w : Fin 4 → A) :
    FrameFan.IsFrameEdge A u w ↔ frameEdge u w := by
  rw [frameEdge, isFrame_iff_firstColumns (by decide : 2 ≤ 4)]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun i => ?_⟩
    funext r
    rw [frame_smul_single_apply]
    fin_cases i
    · exact (hg r).1.symm
    · exact (hg r).2.symm
  · rintro ⟨g, hg⟩
    refine ⟨g, fun r => ⟨?_, ?_⟩⟩
    · have h := congrFun (hg 0) r
      rw [frame_smul_single_apply] at h
      exact h.symm
    · have h := congrFun (hg 1) r
      rw [frame_smul_single_apply] at h
      exact h.symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameFan_isFrameEdge_iff

theorem frameFan_isFrameTriangle_iff (u v w : Fin 4 → A) :
    FrameFan.IsFrameTriangle A u v w ↔ frameTri u v w := by
  rw [frameTri, isFrame_iff_firstColumns (by decide : 3 ≤ 4)]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun i => ?_⟩
    funext r
    rw [frame_smul_single_apply]
    fin_cases i
    · exact (hg r).1.symm
    · exact (hg r).2.1.symm
    · exact (hg r).2.2.symm
  · rintro ⟨g, hg⟩
    refine ⟨g, fun r => ⟨?_, ?_, ?_⟩⟩
    · have h := congrFun (hg 0) r
      rw [frame_smul_single_apply] at h
      exact h.symm
    · have h := congrFun (hg 1) r
      rw [frame_smul_single_apply] at h
      exact h.symm
    · have h := congrFun (hg 2) r
      rw [frame_smul_single_apply] at h
      exact h.symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameFan_isFrameTriangle_iff

/-- Lane 10's frame vertices are lane 07's frame vertices. -/
def frameVertexFourEquiv : FrameFan.FrameVertex A ≃ FrameVertices A 4 where
  toFun u := ⟨u.1, (frameFan_isFrameVertex_iff u.1).1 u.2⟩
  invFun u := ⟨u.1, (frameFan_isFrameVertex_iff u.1).2 u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexFourEquiv

theorem frameComplexFour_edge_iff (u w : FrameFan.FrameVertex A) :
    (FrameFan.frameComplexFour A).edge u w ↔
      (frameComplex A 4).edge (frameVertexFourEquiv u) (frameVertexFourEquiv w) :=
  frameFan_isFrameEdge_iff u.1 w.1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplexFour_edge_iff

theorem frameComplexFour_tri_iff (u v w : FrameFan.FrameVertex A) :
    (FrameFan.frameComplexFour A).tri u v w ↔
      (frameComplex A 4).tri (frameVertexFourEquiv u) (frameVertexFourEquiv v)
        (frameVertexFourEquiv w) :=
  frameFan_isFrameTriangle_iff u.1 v.1 w.1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplexFour_tri_iff

/-- `GL_4(A)` acts on lane 10's frame vertices. -/
instance frameFanVertexMulAction :
    MulAction (Matrix (Fin 4) (Fin 4) A)ˣ (FrameFan.FrameVertex A) where
  smul g u := ⟨g • u.1,
    (frameFan_isFrameVertex_iff (g • u.1)).2 (((frameFan_isFrameVertex_iff u.1).1 u.2).smul g)⟩
  one_smul u := Subtype.ext (one_smul _ u.1)
  mul_smul g h u := Subtype.ext (mul_smul g h u.1)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameFanVertexMulAction

theorem frameFanVertex_smul_val (g : (Matrix (Fin 4) (Fin 4) A)ˣ) (u : FrameFan.FrameVertex A) :
    (g • u).1 = g • u.1 := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameFanVertex_smul_val

theorem frameVertexFourEquiv_smul (g : (Matrix (Fin 4) (Fin 4) A)ˣ) (u : FrameFan.FrameVertex A) :
    frameVertexFourEquiv (g • u) = g • frameVertexFourEquiv u := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertexFourEquiv_smul

/-- `GL_4(A)` preserves the ordered edges and triangles of lane 10's `frameComplexFour`. -/
theorem frameComplexFour_action :
    (FrameFan.frameComplexFour A).Action (Matrix (Fin 4) (Fin 4) A)ˣ where
  edge_smul := fun g {a b} h =>
    (frameFan_isFrameEdge_iff (g • a.1) (g • b.1)).2
      (((frameFan_isFrameEdge_iff a.1 b.1).1 h).smul g)
  tri_smul := fun g {a b c} h =>
    (frameFan_isFrameTriangle_iff (g • a.1) (g • b.1) (g • c.1)).2
      (((frameFan_isFrameTriangle_iff a.1 b.1 c.1).1 h).smul g)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplexFour_action

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
