import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.Fan
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Logic.Equiv.Basic
import GroupApproximation.Leavitt.UniversalLeavitt
import GroupApproximation.Meta.AxiomGuard

/-!
# `X_4(L)` is simply connected, modulo the rank-four frame cone

Lane `sk-leavitt-10`.  Khanh (arXiv:2609.08428v1), tex l.539: "The complex $X_4(R)$ is the
ordered frame complex used in Proposition~\ref{prop:frame-cone}, with complements forgotten.
According to that proposition, any finite collection of vertices and edges has a common apex
... Thus $|X_4(R)|$ is connected and simply connected."  Tex l.360 (`prop:frame-cone`): "For a
finite family of simplices of $X_r(R)$, each having at most $r-2$ frame vectors, there is a
single vector $v$ extending every frame in the family to a simplex of $X_r(R)$."

## Route

* A `k`-frame (`k ≤ 3`) is the list of the first `k` columns of a unit of `M_4(A)`, which is
  Khanh's decomposition `A^4 = v_1A ⊕ ⋯ ⊕ v_kA ⊕ C` with complements forgotten.
  `exists_unit_permCols` permutes columns, so every face of a triangle frame is an edge frame.
* `frameComplexFour A`: the lane-06 `OrderedTwoComplex` on the frame vertices.
* `FrameConeFourStatement A` is `FrameFan.HasFanApex (frameComplexFour A)` spelled out: Khanh
  Prop 4.2 at `r = 4`, restricted to the empty frame, the 1-frames and the 2-frames of the
  family.  The fan (`FrameFan.simplyConnected_of_hasFanApex`) is proved in full.

## Truth check and remaining gap

* **Correction.**  The lane line asks for `(frameComplex L 4).SimplyConnected` with vertex type
  `Fin 4 → L`.  With lane 06's `SimplyConnected := Connected ∧ …`, that statement is false: the
  zero vector lies on no edge frame (a unit has no zero column once `L ≠ 0`), so no edge path
  joins it to `e_0`.  The true statement, proved here modulo the cone, takes the frame vertices
  `FrameVertex A = {u // IsFrameVertex A u}` as vertex type.  Lane 07's `frameComplex` is not on
  disk, so this module defines its own complex.
* **Gap.**  `BinaryLeavittFrameConeFourStatement` is lane 09's interface (`frame_cone_four`,
  not on disk).  It is true by Khanh Prop 4.2 with `r = 4`, applied to the family `[]`, `[u]`,
  `[u, w]` (every listed simplex has `≤ 2 = r - 2` vectors; the extended `[]` is the apex
  vertex).  Its proof content (word multiplier, sibling kernel, cone coordinates) is strictly
  smaller than the target, which also needs the fan, the homotopy induction and the
  column-permutation faces, all proved here.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan

universe v

variable (A : Type v) [Ring A]

/-- A 1-frame of `A^4`: the first column of some invertible `4 × 4` matrix. -/
def IsFrameVertex (u : Fin 4 → A) : Prop :=
  ∃ g : (Matrix (Fin 4) (Fin 4) A)ˣ, ∀ r, (g : Matrix (Fin 4) (Fin 4) A) r 0 = u r

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.IsFrameVertex

/-- An ordered 2-frame `(u,w)` of `A^4`: the first two columns of some invertible matrix. -/
def IsFrameEdge (u w : Fin 4 → A) : Prop :=
  ∃ g : (Matrix (Fin 4) (Fin 4) A)ˣ, ∀ r,
    (g : Matrix (Fin 4) (Fin 4) A) r 0 = u r ∧ (g : Matrix (Fin 4) (Fin 4) A) r 1 = w r

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.IsFrameEdge

/-- An ordered 3-frame `(u,v,w)` of `A^4`: the first three columns of some invertible matrix. -/
def IsFrameTriangle (u v w : Fin 4 → A) : Prop :=
  ∃ g : (Matrix (Fin 4) (Fin 4) A)ˣ, ∀ r,
    (g : Matrix (Fin 4) (Fin 4) A) r 0 = u r ∧ (g : Matrix (Fin 4) (Fin 4) A) r 1 = v r ∧
      (g : Matrix (Fin 4) (Fin 4) A) r 2 = w r

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.IsFrameTriangle

/-- The vertices of `X_4(A)`: the 1-frames. -/
abbrev FrameVertex : Type v := {u : Fin 4 → A // IsFrameVertex A u}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.FrameVertex

variable {A}

/-- Permuting the columns of an invertible matrix gives an invertible matrix. -/
theorem exists_unit_permCols (g : (Matrix (Fin 4) (Fin 4) A)ˣ) (σ : Equiv.Perm (Fin 4)) :
    ∃ g' : (Matrix (Fin 4) (Fin 4) A)ˣ, ∀ r j,
      (g' : Matrix (Fin 4) (Fin 4) A) r j = (g : Matrix (Fin 4) (Fin 4) A) r (σ j) := by
  refine ⟨⟨(g : Matrix (Fin 4) (Fin 4) A).submatrix id σ,
    ((g⁻¹ : (Matrix (Fin 4) (Fin 4) A)ˣ) : Matrix (Fin 4) (Fin 4) A).submatrix σ id, ?_, ?_⟩,
    fun _ _ => rfl⟩
  · exact (Matrix.submatrix_mul (g : Matrix (Fin 4) (Fin 4) A)
      ((g⁻¹ : (Matrix (Fin 4) (Fin 4) A)ˣ) : Matrix (Fin 4) (Fin 4) A) id (σ : Fin 4 → Fin 4) id
      σ.bijective).symm.trans
        ((congrArg (fun M : Matrix (Fin 4) (Fin 4) A => M.submatrix id id) g.mul_inv).trans
          (Matrix.submatrix_id_id (1 : Matrix (Fin 4) (Fin 4) A)))
  · exact (Matrix.submatrix_mul
      ((g⁻¹ : (Matrix (Fin 4) (Fin 4) A)ˣ) : Matrix (Fin 4) (Fin 4) A)
      (g : Matrix (Fin 4) (Fin 4) A) (σ : Fin 4 → Fin 4) id (σ : Fin 4 → Fin 4)
      Function.bijective_id).symm.trans
        ((congrArg (fun M : Matrix (Fin 4) (Fin 4) A => M.submatrix σ σ) g.inv_mul).trans
          (Matrix.submatrix_one_equiv σ))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.exists_unit_permCols

theorem IsFrameTriangle.edge01 {u v w : Fin 4 → A} (h : IsFrameTriangle A u v w) :
    IsFrameEdge A u v := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun r => ⟨(hg r).1, (hg r).2.1⟩⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.IsFrameTriangle.edge01

theorem IsFrameTriangle.edge12 {u v w : Fin 4 → A} (h : IsFrameTriangle A u v w) :
    IsFrameEdge A v w := by
  obtain ⟨g, hg⟩ := h
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  obtain ⟨g₁, hg₁⟩ := exists_unit_permCols g (Equiv.swap 0 1)
  obtain ⟨g₂, hg₂⟩ := exists_unit_permCols g₁ (Equiv.swap 1 2)
  refine ⟨g₂, fun r => ⟨?_, ?_⟩⟩
  · rw [hg₂ r 0, Equiv.swap_apply_of_ne_of_ne h01 h02, hg₁ r 0, Equiv.swap_apply_left]
    exact (hg r).2.1
  · rw [hg₂ r 1, Equiv.swap_apply_left, hg₁ r 2, Equiv.swap_apply_of_ne_of_ne h20 h21]
    exact (hg r).2.2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.IsFrameTriangle.edge12

theorem IsFrameTriangle.edge02 {u v w : Fin 4 → A} (h : IsFrameTriangle A u v w) :
    IsFrameEdge A u w := by
  obtain ⟨g, hg⟩ := h
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  obtain ⟨g', hg'⟩ := exists_unit_permCols g (Equiv.swap 1 2)
  refine ⟨g', fun r => ⟨?_, ?_⟩⟩
  · rw [hg' r 0, Equiv.swap_apply_of_ne_of_ne h01 h02]
    exact (hg r).1
  · rw [hg' r 1, Equiv.swap_apply_left]
    exact (hg r).2.2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.IsFrameTriangle.edge02

variable (A)

/-- The ordered frame complex `X_4(A)` (2-skeleton, complements forgotten), on frame vertices. -/
def frameComplexFour : OrderedTwoComplex (FrameVertex A) where
  edge u w := IsFrameEdge A u.1 w.1
  tri u v w := IsFrameTriangle A u.1 v.1 w.1
  tri_edge01 h := IsFrameTriangle.edge01 h
  tri_edge12 h := IsFrameTriangle.edge12 h
  tri_edge02 h := IsFrameTriangle.edge02 h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.frameComplexFour

/-- Khanh Prop 4.2 at `r = 4` for vertices and edges (lane 09's interface): every finite list of
frame vertices and ordered edge frames has one apex vertex `c` with `(c,u)` an edge frame for each
listed vertex `u` and `(c,u,w)` a triangle frame for each listed edge `(u,w)`. -/
def FrameConeFourStatement : Prop :=
  ∀ (vs : List (FrameVertex A)) (es : List (FrameVertex A × FrameVertex A)),
    (∀ x ∈ es, IsFrameEdge A x.1.1 x.2.1) →
      ∃ c : FrameVertex A, (∀ w ∈ vs, IsFrameEdge A c.1 w.1) ∧
        ∀ x ∈ es, IsFrameTriangle A c.1 x.1.1 x.2.1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.FrameConeFourStatement

/-- The fan (tex l.539): the rank-four frame cone makes `X_4(A)` simply connected. -/
theorem frameComplexFour_simplyConnected_of_frameConeFour (h : FrameConeFourStatement A) :
    (frameComplexFour A).SimplyConnected :=
  simplyConnected_of_hasFanApex (X := frameComplexFour A) h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.frameComplexFour_simplyConnected_of_frameConeFour

/-- The frame cone at rank four over the binary Leavitt algebra `L = L_𝔽₂(1,2)`. -/
def BinaryLeavittFrameConeFourStatement : Prop :=
  FrameConeFourStatement (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.BinaryLeavittFrameConeFourStatement

/-- Lane `sk-leavitt-10` endpoint: `X_4(L)` is simply connected, given the rank-four frame cone
over `L` (lane 09). -/
theorem binaryLeavitt_frameComplexFour_simplyConnected_of_frameConeFour
    (h : BinaryLeavittFrameConeFourStatement) :
    (frameComplexFour
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).SimplyConnected :=
  frameComplexFour_simplyConnected_of_frameConeFour _ h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.binaryLeavitt_frameComplexFour_simplyConnected_of_frameConeFour

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan
