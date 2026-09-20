import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Setup
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94FaceArcFit
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassProducerGaps
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSpurEnclosure
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Case A: the gap walk encloses a cell-free pocket

With `m ≠ 0`, the gap walk `c = seg (facePerm a) m` of the cell `C` closes by a first turn past `b`
and `α a`.  If the outer face is reached from `b` in the joined map, it is not enclosed, so `c` is
the outside walk of an enclosed face set; `c` is an arc of `C`, and `C` is not enclosed.  Under the
hypothesis `NoCellInside` no relator cell is enclosed, so the reversed walk, the gap, reads `1`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

/-- A point fixed by `p^r` is moved by `p^(k + r)` like by `p^k`. -/
theorem pow_add_apply_of_fix {α : Type*} {p : Perm α} {x : α} {r : ℕ} (h : (p ^ r) x = x)
    (k : ℕ) : (p ^ (k + r)) x = (p ^ k) x := by
  rw [pow_add, Perm.mul_apply, h]

section Gap

variable {M : CombMap.{v}} {a b : M.Dart} {m : ℕ}

theorem mem_gapSeg {y : M.Dart} (hy : y ∈ seg M (M.facePerm a) m) :
    ∃ t < m, (M.facePerm ^ (t + 1)) a = y := by
  obtain ⟨r, hr, rfl⟩ := mem_seg.mp hy
  exact ⟨r, hr, pow_succ_apply' _ _ _⟩

theorem faceOf_of_mem_gapSeg {y : M.Dart} (hy : y ∈ seg M (M.facePerm a) m) :
    M.faceOf y = M.faceOf a :=
  (faceOf_of_mem_seg hy).trans (M.faceOf_facePerm a)

/-- The gap walk is nodup. -/
theorem gapSeg_nodup (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b) : (seg M (M.facePerm a) m).Nodup := by
  refine seg_nodup fun r hr0 hrm h => ?_
  apply hleast (m - r) (by omega)
  rw [← hab, pow_succ_apply', pow_succ_apply', ← pow_add_apply_of_fix h (m - r),
    Nat.sub_add_cancel hrm.le]

theorem gapSeg_getLast (hm : m ≠ 0) :
    (seg M (M.facePerm a) m).getLast (seg_ne_nil hm) = (M.facePerm ^ m) a := by
  rw [seg_getLast hm, ← pow_succ_apply', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]

/-- `b` is off the edges of the gap walk. -/
theorem not_walkKeep_b (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b)
    (hface : M.faceOf (M.alpha b) ≠ M.faceOf a) : ¬ walkKeep M (seg M (M.facePerm a) m) b := by
  rintro (h | h)
  · obtain ⟨t, ht, heq⟩ := mem_gapSeg h
    exact hleast t ht heq
  · exact hface (faceOf_of_mem_gapSeg h)

/-- `α a` is off the edges of the gap walk. -/
theorem not_walkKeep_alpha_a (hb : M.sigma b = M.alpha a) (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b)
    (hface : M.faceOf (M.alpha b) ≠ M.faceOf a) :
    ¬ walkKeep M (seg M (M.facePerm a) m) (M.alpha a) := by
  rintro (h | h)
  · exact hface ((JunctionPocket.faceOf_alpha_a hb).symm.trans (faceOf_of_mem_gapSeg h))
  · rw [M.alpha_involutive a] at h
    obtain ⟨t, ht, heq⟩ := mem_gapSeg h
    exact JunctionPocket.gap_ne_start hab hleast ht heq

/-- **The gap walk closes** by a first turn from its last dart past `b` and `α a`. -/
theorem gapSeg_firstTurn (hm : m ≠ 0) (hb : M.sigma b = M.alpha a)
    (hab : (M.facePerm ^ (m + 1)) a = b) (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b)
    (hface : M.faceOf (M.alpha b) ≠ M.faceOf a) :
    FirstTurn M (seg M (M.facePerm a) m) ((seg M (M.facePerm a) m).getLast (seg_ne_nil hm))
      ((seg M (M.facePerm a) m).head (seg_ne_nil hm)) := by
  rw [gapSeg_getLast hm, seg_head hm]
  exact firstTurn_three (JunctionPocket.facePerm_last hab) hb rfl (not_walkKeep_b hleast hface)
    (not_walkKeep_alpha_a hb hab hleast hface)

end Gap

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The reversed gap walk is the gap. -/
theorem invDarts_gapSeg (X : DiscDiagram.{u, w, v} W) (a : X.toCombMap.Dart) (m : ℕ) :
    invDarts X (seg X.toCombMap (X.toCombMap.facePerm a) m) =
      ((List.range m).map fun t =>
        X.toCombMap.alpha ((X.toCombMap.facePerm ^ (t + 1)) a)).reverse := by
  unfold invDarts seg
  rw [List.map_reverse, List.map_map]
  congr 1

/-- **No relator cell inside a pocket along a cell.**  An enclosed face set whose outside walk is an
arc of a relator cell that is not enclosed holds no relator cell.  Discharged in `Proof.lean`
through the loop cut and the clause below the number of relator cells. -/
def NoCellInside (X : DiscDiagram.{u, w, v} W) : Prop :=
  ∀ (F : Finset X.toCombMap.Face) (walk : List X.toCombMap.Dart), EnclosedFaceSetSucc X F walk →
    ∀ j : Fin X.rCellCount, (cell X j).face ∉ F →
    ∀ A : CyclicArc (cellDarts X j), A.darts = walk →
    ∀ C ∈ X.relatorCells, C.face ∉ F

/-- A nodup face walk of a cell is an arc of the cell. -/
theorem exists_arc_gapSeg (X : DiscDiagram.{u, w, v} W) {a b : X.toCombMap.Dart} {m : ℕ}
    (hab : (X.toCombMap.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (X.toCombMap.facePerm ^ (t + 1)) a ≠ b) (j : Fin X.rCellCount)
    (ha : a ∈ cellDarts X j) :
    ∃ A : CyclicArc (cellDarts X j), A.darts = seg X.toCombMap (X.toCombMap.facePerm a) m := by
  have hCa : X.toCombMap.faceOf a = (cell X j).face :=
    ((X.faceBoundary (cell X j).face).mem_iff a).mp ha
  have hsub : seg X.toCombMap (X.toCombMap.facePerm a) m ⊆ cellDarts X j := fun y hy =>
    ((X.faceBoundary (cell X j).face).mem_iff y).mpr ((faceOf_of_mem_gapSeg hy).trans hCa)
  have hlen := ((gapSeg_nodup hab hleast).subperm hsub).length_le
  rw [length_seg] at hlen
  have hd : X.toCombMap.facePerm a ∈ cellDarts X j :=
    ((X.faceBoundary (cell X j).face).mem_iff _).mpr ((X.toCombMap.faceOf_facePerm a).trans hCa)
  obtain ⟨A, hA⟩ := CyclicArc.exists_darts_eq_map_pow X j hd hlen
  exact ⟨A, hA⟩

/-- The outer face is not enclosed by the gap walk when the outer dart is on the face side. -/
theorem outerFace_not_mem_gapSeg (X : DiscDiagram.{u, w, v} W) {a b o : X.toCombMap.Dart}
    {m : ℕ} (hm : m ≠ 0) (hb : X.toCombMap.sigma b = X.toCombMap.alpha a)
    (hab : (X.toCombMap.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (X.toCombMap.facePerm ^ (t + 1)) a ≠ b)
    (hface : X.toCombMap.faceOf (X.toCombMap.alpha b) ≠ X.toCombMap.faceOf a)
    (ho : X.toCombMap.faceOf o = X.outerFace)
    (hJ : Relation.EqvGen (FoldMap.joined X.toCombMap ((X.toCombMap.facePerm ^ m) a) a).Adjacent
      b o) :
    X.outerFace ∉ enclosedFaces X.toCombMap (seg X.toCombMap (X.toCombMap.facePerm a) m) := by
  intro hout
  have hc := seg_ne_nil (M := X.toCombMap) (x := X.toCombMap.facePerm a) hm
  have hclose := gapSeg_firstTurn hm hb hab hleast hface
  have hnot : ∀ y ∈ seg X.toCombMap (X.toCombMap.facePerm a) m,
      X.toCombMap.faceOf y ∉
        enclosedFaces X.toCombMap (seg X.toCombMap (X.toCombMap.facePerm a) m) :=
    fun y hy => faceOf_not_mem_of_chain X.planar hc (seg_isChain _ _) hclose hy
  have hfa : X.toCombMap.facePerm a ∈ seg X.toCombMap (X.toCombMap.facePerm a) m :=
    mem_seg.mpr ⟨0, Nat.pos_of_ne_zero hm, by rw [pow_zero, Perm.one_apply]⟩
  have hCnot := hnot _ hfa
  rw [X.toCombMap.faceOf_facePerm] at hCnot
  have hpnot : X.toCombMap.faceOf ((X.toCombMap.facePerm ^ m) a) ∉
      enclosedFaces X.toCombMap (seg X.toCombMap (X.toCombMap.facePerm a) m) := by
    rw [JunctionPocket.faceOf_pow_apply]
    exact hCnot
  have hseed := seed_of_reach (c := seg X.toCombMap (X.toCombMap.facePerm a) m)
    (p := (X.toCombMap.facePerm ^ m) a) (a := a) (r := X.toCombMap.facePerm a)
    fun y hy => by
      obtain ⟨t, ht, rfl⟩ := mem_gapSeg hy
      exact JunctionPocket.reach_gap hab hleast ht
  have hreach := reach_of_enclosed hpnot hCnot hseed (x := o) (by rw [ho]; exact hout)
  exact JunctionPocket.junction_not_reach X.planar hm hb hab hleast
    (.trans _ _ _ hJ (.symm _ _ hreach))

/-- **Case A: the gap reads `1`.**  With the outer dart on the face side of the corner, the gap walk
encloses a face set without the cell `C`, and so without relator cells. -/
theorem listVal_gap_eq_one (X : DiscDiagram.{u, w, v} W) (hNo : NoCellInside X)
    {a b o : X.toCombMap.Dart} {m : ℕ} (hm : m ≠ 0)
    (hb : X.toCombMap.sigma b = X.toCombMap.alpha a)
    (hab : (X.toCombMap.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (X.toCombMap.facePerm ^ (t + 1)) a ≠ b)
    (hface : X.toCombMap.faceOf (X.toCombMap.alpha b) ≠ X.toCombMap.faceOf a)
    (j : Fin X.rCellCount) (ha : a ∈ cellDarts X j) (ho : X.toCombMap.faceOf o = X.outerFace)
    (hJ : Relation.EqvGen (FoldMap.joined X.toCombMap ((X.toCombMap.facePerm ^ m) a) a).Adjacent
      b o) :
    RelLetter.listVal (dartWord X ((List.range m).map fun t =>
      X.toCombMap.alpha ((X.toCombMap.facePerm ^ (t + 1)) a)).reverse) = 1 := by
  have hc := seg_ne_nil (M := X.toCombMap) (x := X.toCombMap.facePerm a) hm
  have hclose := gapSeg_firstTurn hm hb hab hleast hface
  have hE := enclosedFaceSetSucc_of_chain X hc (gapSeg_nodup hab hleast) (seg_isChain _ _) hclose
    (outerFace_not_mem_gapSeg X hm hb hab hleast hface ho hJ)
  have hfa : X.toCombMap.facePerm a ∈ seg X.toCombMap (X.toCombMap.facePerm a) m :=
    mem_seg.mpr ⟨0, Nat.pos_of_ne_zero hm, by rw [pow_zero, Perm.one_apply]⟩
  have hCout : (cell X j).face ∉
      enclosedFaces X.toCombMap (seg X.toCombMap (X.toCombMap.facePerm a) m) := by
    have h := faceOf_not_mem_of_chain X.planar hc (seg_isChain _ _) hclose hfa
    rwa [X.toCombMap.faceOf_facePerm, ((X.faceBoundary (cell X j).face).mem_iff a).mp ha] at h
  obtain ⟨A, hA⟩ := exists_arc_gapSeg X hab hleast j ha
  have hval := SameCellSpurEnclosure.listVal_eq_one_of_enclosedSucc
    closedWalkEnclosedSubdiagramSucc hE (hNo _ _ hE j hCout A hA)
  rwa [invDarts_gapSeg] at hval

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.pow_add_apply_of_fix
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.mem_gapSeg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.faceOf_of_mem_gapSeg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.gapSeg_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.gapSeg_getLast
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.not_walkKeep_b
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.not_walkKeep_alpha_a
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.gapSeg_firstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.invDarts_gapSeg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.NoCellInside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.exists_arc_gapSeg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.outerFace_not_mem_gapSeg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.listVal_gap_eq_one
