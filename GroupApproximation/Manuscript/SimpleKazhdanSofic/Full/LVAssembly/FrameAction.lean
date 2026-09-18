import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.Triangle
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.Action
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.FrameFour

/-!
# `GL_4(L)` acting on the frame complex (glue for `K₂(4, L) = ⊥`)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  This is part of the proof of
Khanh (arXiv:2609.08428), Thm 5.1.  `GL_4(L)` acts on the unimodular vectors of `L⁴` by
`g • u = g u`.  The action preserves ordered frames, and it is transitive on ordered edges and on
ordered triangles.  These are the action inputs of Brown's criterion
`GroupApproximation.Full.LVBrown.brown_lift` for the complex
`GroupApproximation.Full.LVFrame.frameComplexFour L`.

* `frameMulAction`, `frameAction`: the action, which preserves edges and triangles.
* `baseVertex = e₃`, `nextVertex = e₂`, `thirdVertex = e₁`, and `baseEdge`.
* `frame_edge_transitive`, `frame_tri_transitive`: a frame is the image of the base frame.
* `elementaryUnit_mulVec`, `fix_single`, `add_single`, `cancel_single`: `1 + E_{ij}` on basis
  vectors.  `swapMid_smul_next`: `h e₂ = e₁`.
-/

namespace GroupApproximation.Full.LVAssembly

open scoped Matrix
open GroupApproximation.Full.LVFrame

noncomputable section

/-- `(M e_c)_r = M_{rc}`. -/
theorem mulVec_single_apply (M : Matrix (Fin 4) (Fin 4) BinL) (c r : Fin 4) :
    (M *ᵥ Pi.single c 1) r = M r c := by
  rw [Matrix.mulVec_single_one, Matrix.col_apply]

/-- If column `c` of `M` is `u`, then column `c` of `g M` is `g u`. -/
theorem col_mul_eq {M : Matrix (Fin 4) (Fin 4) BinL} {c : Fin 4} {u : Fin 4 → BinL}
    (hM : ∀ r, M r c = u r) (g : Matrix (Fin 4) (Fin 4) BinL) (r : Fin 4) :
    (g * M) r c = (g *ᵥ u) r := by
  have hu : M *ᵥ Pi.single c 1 = u := funext fun p => by rw [mulVec_single_apply, hM p]
  rw [← mulVec_single_apply (g * M) c r, ← Matrix.mulVec_mulVec, hu]

/-- An invertible matrix maps unimodular vectors to unimodular vectors. -/
theorem isFrameVertex_mulVec (g : GLFour) {u : Fin 4 → BinL} (hu : IsFrameVertex BinL u) :
    IsFrameVertex BinL ((g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ u) := by
  obtain ⟨M, hM⟩ := hu
  refine ⟨g * M, fun r => ?_⟩
  rw [Units.val_mul]
  exact col_mul_eq hM (g : Matrix (Fin 4) (Fin 4) BinL) r

/-- **`GL_4(L)` acts on the vertices of the frame complex** by `g • u = g u` (Khanh, Thm 5.1). -/
instance frameMulAction : MulAction GLFour (FrameVertex BinL) where
  smul g u := ⟨(g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ u.1, isFrameVertex_mulVec g u.2⟩
  one_smul u := Subtype.ext
    (show ((1 : GLFour) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ u.1 = u.1 by
      rw [Units.val_one, Matrix.one_mulVec])
  mul_smul g g' u := Subtype.ext
    (show ((g * g' : GLFour) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ u.1 =
        (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ ((g' : Matrix (Fin 4) (Fin 4) BinL) *ᵥ u.1) by
      rw [Units.val_mul, Matrix.mulVec_mulVec])

theorem smul_val (g : GLFour) (u : FrameVertex BinL) :
    (g • u).1 = (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ u.1 :=
  rfl

/-- **The action preserves ordered edges and triangles** (Khanh, Thm 5.1; tex l.733-735). -/
theorem frameAction : (frameComplexFour BinL).Action GLFour := by
  constructor
  · intro g a b hab
    obtain ⟨M, hM⟩ : IsFrameEdge BinL a.1 b.1 := hab
    show IsFrameEdge BinL ((g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ a.1)
      ((g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ b.1)
    refine ⟨g * M, fun r => ⟨?_, ?_⟩⟩
    · rw [Units.val_mul]
      exact col_mul_eq (fun p => (hM p).1) (g : Matrix (Fin 4) (Fin 4) BinL) r
    · rw [Units.val_mul]
      exact col_mul_eq (fun p => (hM p).2) (g : Matrix (Fin 4) (Fin 4) BinL) r
  · intro g a b c habc
    obtain ⟨M, hM⟩ : IsFrameTriangle BinL a.1 b.1 c.1 := habc
    show IsFrameTriangle BinL ((g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ a.1)
      ((g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ b.1) ((g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ c.1)
    refine ⟨g * M, fun r => ⟨?_, ?_, ?_⟩⟩
    · rw [Units.val_mul]
      exact col_mul_eq (fun p => (hM p).1) (g : Matrix (Fin 4) (Fin 4) BinL) r
    · rw [Units.val_mul]
      exact col_mul_eq (fun p => (hM p).2.1) (g : Matrix (Fin 4) (Fin 4) BinL) r
    · rw [Units.val_mul]
      exact col_mul_eq (fun p => (hM p).2.2) (g : Matrix (Fin 4) (Fin 4) BinL) r

theorem rev_zero_four : Fin.revPerm (0 : Fin 4) = 3 := by decide

theorem rev_one_four : Fin.revPerm (1 : Fin 4) = 2 := by decide

theorem rev_two_four : Fin.revPerm (2 : Fin 4) = 1 := by decide

theorem rev_three_four : Fin.revPerm (3 : Fin 4) = 0 := by decide

/-- A basis vector is unimodular. -/
theorem isFrameVertex_single (c : Fin 4) : IsFrameVertex BinL (Pi.single c 1) := by
  obtain ⟨g, hg⟩ := exists_unit_permCols (1 : GLFour) (Equiv.swap 0 c)
  refine ⟨g, fun r => ?_⟩
  rw [hg r 0, Equiv.swap_apply_left, Units.val_one, Matrix.one_apply, Pi.single_apply]

/-- **The base vertex `e₃`** (Khanh, Thm 5.1). -/
def baseVertex : FrameVertex BinL := ⟨lastCol, isFrameVertex_single 3⟩

/-- The second vertex `e₂` of the base edge. -/
def nextVertex : FrameVertex BinL := ⟨prevCol, isFrameVertex_single 2⟩

/-- The third vertex `e₁` of the base triangle. -/
def thirdVertex : FrameVertex BinL := ⟨Pi.single 1 1, isFrameVertex_single 1⟩

/-- **The base edge `(e₃, e₂)`**. -/
theorem baseEdge : (frameComplexFour BinL).edge baseVertex nextVertex := by
  show IsFrameEdge BinL (Pi.single 3 1) (Pi.single 2 1)
  obtain ⟨g, hg⟩ := exists_unit_permCols (1 : GLFour) Fin.revPerm
  refine ⟨g, fun r => ⟨?_, ?_⟩⟩
  · rw [hg r 0, rev_zero_four, Units.val_one, Matrix.one_apply, Pi.single_apply]
  · rw [hg r 1, rev_one_four, Units.val_one, Matrix.one_apply, Pi.single_apply]

/-- If the columns of `g` are those of `M` in reverse order, then `g e_c` is column `rev c`
of `M`. -/
theorem smul_single_eq {g M : GLFour}
    (hg : ∀ r j, (g : Matrix (Fin 4) (Fin 4) BinL) r j =
      (M : Matrix (Fin 4) (Fin 4) BinL) r (Fin.revPerm j))
    {c : Fin 4} {u : Fin 4 → BinL} (hu : ∀ r, (M : Matrix (Fin 4) (Fin 4) BinL) r (Fin.revPerm c) = u r) :
    (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single c 1 = u :=
  funext fun r => by
    rw [mulVec_single_apply, hg r c]
    exact hu r

/-- **`GL_4(L)` is transitive on ordered edges** (Khanh, Thm 5.1; tex l.733-735). -/
theorem frame_edge_transitive : ∀ a b : FrameVertex BinL, (frameComplexFour BinL).edge a b →
    ∃ g : GLFour, g • baseVertex = a ∧ g • nextVertex = b := by
  intro a b hab
  obtain ⟨M, hM⟩ : IsFrameEdge BinL a.1 b.1 := hab
  obtain ⟨g, hg⟩ := exists_unit_permCols M Fin.revPerm
  refine ⟨g, Subtype.ext ?_, Subtype.ext ?_⟩
  · show (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 3 1 = a.1
    exact smul_single_eq hg fun r => by
      rw [rev_three_four]
      exact (hM r).1
  · show (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 2 1 = b.1
    exact smul_single_eq hg fun r => by
      rw [rev_two_four]
      exact (hM r).2

/-- `1 + E_{ij}(a)` applied to a vector. -/
theorem elementaryUnit_mulVec (i j : Fin 4) (hij : i ≠ j) (a : BinL) (v : Fin 4 → BinL) :
    (GroupApproximation.elementaryUnit i j hij a : Matrix (Fin 4) (Fin 4) BinL) *ᵥ v =
      v + (a * v j) • Pi.single i 1 := by
  show (1 + Matrix.single i j a) *ᵥ v = v + (a * v j) • Pi.single i 1
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]

/-- `1 + E_{ij}` fixes `e_c` for `j ≠ c`. -/
theorem fix_single (i j : Fin 4) (hij : i ≠ j) {c : Fin 4} (hc : j ≠ c) :
    (GroupApproximation.elementaryUnit i j hij (1 : BinL) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ
      Pi.single c 1 = Pi.single c 1 := by
  rw [elementaryUnit_mulVec, Pi.single_eq_of_ne hc, mul_zero, zero_smul, add_zero]

/-- `(1 + E_{ij}) e_j = e_j + e_i`. -/
theorem add_single (i j : Fin 4) (hij : i ≠ j) :
    (GroupApproximation.elementaryUnit i j hij (1 : BinL) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ
      Pi.single j 1 = Pi.single j 1 + Pi.single i 1 := by
  rw [elementaryUnit_mulVec, Pi.single_eq_same, one_mul, one_smul]

/-- In characteristic two, `v + v = 0`. -/
theorem add_self_binL (v : Fin 4 → BinL) : v + v = 0 := by
  funext r
  rw [Pi.add_apply, Pi.zero_apply, ← two_mul, two_eq_zero_binL, zero_mul]

/-- `(1 + E_{ij}) (e_i + e_j) = e_j` in characteristic two. -/
theorem cancel_single (i j : Fin 4) (hij : i ≠ j) :
    (GroupApproximation.elementaryUnit i j hij (1 : BinL) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ
      (Pi.single i 1 + Pi.single j 1) = Pi.single j 1 := by
  rw [elementaryUnit_mulVec, Pi.add_apply, Pi.single_eq_of_ne hij.symm, Pi.single_eq_same,
    zero_add, one_mul, one_smul, add_comm (Pi.single i 1 : Fin 4 → BinL) (Pi.single j 1),
    add_assoc, add_self_binL, add_zero]

/-- **`h e₂ = e₁`**, for `h = swapMid` (Khanh, Thm 5.1). -/
theorem swapMid_smul_next : swapMid • nextVertex = thirdVertex := by
  refine Subtype.ext ?_
  show (swapMid : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 2 1 = Pi.single 1 1
  rw [swapMid_eq, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    fix_single 2 1 midIdx_ne (show (1 : Fin 4) ≠ 2 by decide), add_single 1 2 midIdx_ne.symm,
    cancel_single 2 1 midIdx_ne]

/-- **`GL_4(L)` is transitive on ordered triangles**, with base triangle `(e₃, e₂, h e₂)`
(Khanh, Thm 5.1; tex l.733-735). -/
theorem frame_tri_transitive : ∀ a b c : FrameVertex BinL, (frameComplexFour BinL).tri a b c →
    ∃ g : GLFour, g • baseVertex = a ∧ g • nextVertex = b ∧ g • (swapMid • nextVertex) = c := by
  intro a b c habc
  obtain ⟨M, hM⟩ : IsFrameTriangle BinL a.1 b.1 c.1 := habc
  obtain ⟨g, hg⟩ := exists_unit_permCols M Fin.revPerm
  refine ⟨g, Subtype.ext ?_, Subtype.ext ?_, ?_⟩
  · show (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 3 1 = a.1
    exact smul_single_eq hg fun r => by
      rw [rev_three_four]
      exact (hM r).1
  · show (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 2 1 = b.1
    exact smul_single_eq hg fun r => by
      rw [rev_two_four]
      exact (hM r).2.1
  · rw [swapMid_smul_next]
    refine Subtype.ext ?_
    show (g : Matrix (Fin 4) (Fin 4) BinL) *ᵥ Pi.single 1 1 = c.1
    exact smul_single_eq hg fun r => by
      rw [rev_one_four]
      exact (hM r).2.2

end

end GroupApproximation.Full.LVAssembly
