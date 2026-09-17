import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Fan
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Logic.Equiv.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The frame complex `X₄(A)` (leaf T1c)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (leaf T1c of the `K₂(4, L) = ⊥` tree).
Khanh (arXiv:2609.08428), tex l.539: "The complex $X_4(R)$ is the ordered frame complex used in
Proposition 4.2, with complements forgotten."

* A `k`-frame of `A⁴` (`k ≤ 3`) is the list of the first `k` columns of a unit of `M₄(A)`.
* `FrameVertex A`: the unimodular vectors, i.e. the first columns of units.  The vertex type has
  to be this subtype and not all of `A⁴`, because the zero vector lies on no edge and the complex
  on `A⁴` would not be connected.
* `exists_unit_permCols`: permuting the columns of a unit gives a unit.  Hence every face of a
  3-frame is a 2-frame.
* `frameComplexFour A`: the ordered 2-complex whose edges are the 2-frames and whose triangles are
  the 3-frames.
* `frameComplexFour_simplyConnected_of_hasFanApex`: the fan (`Fan.lean`) applied to `X₄(A)`.

This is a port of the unwired foreign module `LeavittK2/FrameFan/FrameComplex.lean`.
-/

namespace GroupApproximation.Full.LVFrame

universe v

variable (A : Type v) [Ring A]

/-- A 1-frame (unimodular vector) of `A⁴`: the first column of some invertible `4 × 4` matrix. -/
def IsFrameVertex (u : Fin 4 → A) : Prop :=
  ∃ g : (Matrix (Fin 4) (Fin 4) A)ˣ, ∀ r, (g : Matrix (Fin 4) (Fin 4) A) r 0 = u r

/-- An ordered 2-frame `(u,w)` of `A⁴`: the first two columns of some invertible matrix. -/
def IsFrameEdge (u w : Fin 4 → A) : Prop :=
  ∃ g : (Matrix (Fin 4) (Fin 4) A)ˣ, ∀ r,
    (g : Matrix (Fin 4) (Fin 4) A) r 0 = u r ∧ (g : Matrix (Fin 4) (Fin 4) A) r 1 = w r

/-- An ordered 3-frame `(u,v,w)` of `A⁴`: the first three columns of some invertible matrix. -/
def IsFrameTriangle (u v w : Fin 4 → A) : Prop :=
  ∃ g : (Matrix (Fin 4) (Fin 4) A)ˣ, ∀ r,
    (g : Matrix (Fin 4) (Fin 4) A) r 0 = u r ∧ (g : Matrix (Fin 4) (Fin 4) A) r 1 = v r ∧
      (g : Matrix (Fin 4) (Fin 4) A) r 2 = w r

/-- The vertices of `X₄(A)`: the unimodular vectors. -/
abbrev FrameVertex : Type v := {u : Fin 4 → A // IsFrameVertex A u}

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

/-- Face `(0,1)` of a 3-frame. -/
theorem IsFrameTriangle.edge01 {u v w : Fin 4 → A} (h : IsFrameTriangle A u v w) :
    IsFrameEdge A u v := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun r => ⟨(hg r).1, (hg r).2.1⟩⟩

/-- Face `(1,2)` of a 3-frame. -/
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

/-- Face `(0,2)` of a 3-frame. -/
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

variable (A)

/-- The ordered frame complex `X₄(A)` on the unimodular vectors (Khanh, tex l.539; its 2-skeleton,
with complements forgotten).  Edges are the 2-frames and triangles are the 3-frames. -/
def frameComplexFour : OrderedTwoComplex (FrameVertex A) where
  edge u w := IsFrameEdge A u.1 w.1
  tri u v w := IsFrameTriangle A u.1 v.1 w.1
  tri_edge01 h := IsFrameTriangle.edge01 h
  tri_edge12 h := IsFrameTriangle.edge12 h
  tri_edge02 h := IsFrameTriangle.edge02 h

/-- The fan (Khanh, tex l.539) for `X₄(A)`: if every finite list of vertices and ordered edges of
`X₄(A)` has a common apex, then `X₄(A)` is simply connected. -/
theorem frameComplexFour_simplyConnected_of_hasFanApex (h : HasFanApex (frameComplexFour A)) :
    (frameComplexFour A).SimplyConnected :=
  simplyConnected_of_hasFanApex h

end GroupApproximation.Full.LVFrame
