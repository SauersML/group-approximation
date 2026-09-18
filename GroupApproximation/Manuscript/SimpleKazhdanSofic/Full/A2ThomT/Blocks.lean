import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.Ext
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.SL3Laurent
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.ThomGroup
import GroupApproximation.Kazhdan.SemidirectProductKazhdan
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The structure of Thom's group `G_0(R)` (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2); A. Thom, Groups Geom.
Dyn. 4 (2010), §2.1, proof of Lemma 2.1. Every element of `G_0(R)` has the form
`[[1, uᵀ, d], [0, A, v], [0, 0, 1]]` with `A ∈ SL_3(R)`. This file proves:

* `thomElem u A v d h`: the element of `G_0(R)` with these Thom coordinates;
  `thomElem_mul`: the multiplication law in coordinates.
* `det_eq_det_thomBlock`: a matrix of Thom shape has the determinant of its middle `3 × 3` block.
* `thomBlockHom R : G_0(R) →* SL_3(R)`, the middle block, and `thomBlockHom_surjective`.
* `thom_exists_prod_of_mem_ker`: the kernel `N` (the Heisenberg group) is boundedly generated.
  Every element is `r(u) c(v) r(a) c(w) r(-a) c(-w)` for row and column elements `r`, `c`.
* `thomColHom`, `thomRowHom`: the column copy `(v, A) ↦ [[1,0,0],[0,A,v],[0,0,1]]` and the row copy
  `(n, A) ↦ [[1,nᵀ(A⁻¹)ᵀ,0],[0,(A⁻¹)ᵀ,0],[0,0,1]]` of `R³ ⋊ EL_3(R)` in `G_0(R)`, for the linear
  action `φ A n = A n`.
* `hasRelativePropertyT_thomG0_ker`: relative property (T) for `(R³ ⋊ EL_3(R), R³)` gives
  relative property (T) for `(G_0(R), N)`. Both copies restrict to `R³ → N`, and the kernel
  displacement is at most the sum of six bounded displacements.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation.Full.A2ThomT

open GroupApproximation GroupApproximation.Full.A2Endpoint Matrix

universe u v

noncomputable section

section Coordinates

variable {R : Type u} [CommRing R]

/-- The index `a + 1 ∈ Fin 5` of the middle block, for `a : Fin 3`. -/
def thomIdx (a : Fin 3) : Fin 5 := (Fin.castSucc a).succ

theorem thomIdx_zero : thomIdx (0 : Fin 3) = 1 := rfl

theorem thomIdx_one : thomIdx (1 : Fin 3) = 2 := rfl

theorem thomIdx_two : thomIdx (2 : Fin 3) = 3 := rfl

theorem thomIdx_ne_four (a : Fin 3) : thomIdx a ≠ 4 := by
  fin_cases a <;> decide

/-- The matrix `[[1, uᵀ, d], [0, A, v], [0, 0, 1]]`. -/
def thomMat (u : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) (d : R) :
    Matrix (Fin 5) (Fin 5) R :=
  !![1, u 0, u 1, u 2, d;
     0, A 0 0, A 0 1, A 0 2, v 0;
     0, A 1 0, A 1 1, A 1 2, v 1;
     0, A 2 0, A 2 1, A 2 2, v 2;
     0, 0, 0, 0, 1]

/-- The middle `3 × 3` block of a `5 × 5` matrix. -/
def thomBlock (M : Matrix (Fin 5) (Fin 5) R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun a b => M (thomIdx a) (thomIdx b)

theorem isThomShape_thomMat (u : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (d : R) : IsThomShape (thomMat u A v d) :=
  ⟨fun i => by fin_cases i <;> simp [thomMat, Matrix.one_apply],
    fun j => by fin_cases j <;> simp [thomMat, Matrix.one_apply]⟩

theorem thomBlock_thomMat (u : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (d : R) : thomBlock (thomMat u A v d) = A := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [thomBlock, thomMat, thomIdx_zero, thomIdx_one, thomIdx_two]

/-- A matrix of Thom shape is determined by its Thom coordinates. -/
theorem eq_thomMat {M : Matrix (Fin 5) (Fin 5) R} (hM : IsThomShape M) :
    M = thomMat (fun b => M 0 (thomIdx b)) (thomBlock M) (fun a => M (thomIdx a) 4) (M 0 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thomMat, thomBlock, thomIdx_zero, thomIdx_one, thomIdx_two, hM.col, hM.row,
      Matrix.one_apply]

/-- The multiplication law in Thom coordinates. -/
theorem thomMat_mul (u : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) (d : R)
    (u' : Fin 3 → R) (A' : Matrix (Fin 3) (Fin 3) R) (v' : Fin 3 → R) (d' : R) :
    thomMat u A v d * thomMat u' A' v' d' =
      thomMat (u' + u ᵥ* A') (A * A') (A *ᵥ v' + v) (d' + u ⬝ᵥ v' + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thomMat, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, Matrix.mulVec,
      Matrix.vecMul, dotProduct] <;> ring

theorem thomMat_zero_one : thomMat (0 : Fin 3 → R) 1 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [thomMat, Matrix.one_apply]

theorem thomBlock_mul {M N : Matrix (Fin 5) (Fin 5) R} (hM : IsThomShape M)
    (hN : IsThomShape N) : thomBlock (M * N) = thomBlock M * thomBlock N := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [thomBlock, thomIdx_zero, thomIdx_one, thomIdx_two, Matrix.mul_apply, Fin.sum_univ_five,
      Fin.sum_univ_three, hM.col, hN.row, Matrix.one_apply] <;> ring

theorem thomBlock_one : thomBlock (1 : Matrix (Fin 5) (Fin 5) R) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [thomBlock, thomIdx_zero, thomIdx_one, thomIdx_two, Matrix.one_apply]

/-- A matrix of Thom shape has the determinant of its middle block (expansion along the first
column, then along the last row). -/
theorem det_eq_det_thomBlock {M : Matrix (Fin 5) (Fin 5) R} (hM : IsThomShape M) :
    M.det = (thomBlock M).det := by
  have hcol : ∀ i : Fin 4, M i.succ 0 = 0 := fun i =>
    (hM.col i.succ).trans (Matrix.one_apply_ne (Fin.succ_ne_zero i))
  have h00 : M 0 0 = 1 := (hM.col 0).trans (Matrix.one_apply_eq 0)
  have h1 : M.det = (M.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [hcol, h00]
  have hrow : ∀ j : Fin 3, M.submatrix Fin.succ Fin.succ (Fin.last 3) (Fin.castSucc j) = 0 :=
    fun j => (hM.row (thomIdx j)).trans (Matrix.one_apply_ne (thomIdx_ne_four j).symm)
  have h44 : M.submatrix Fin.succ Fin.succ (Fin.last 3) (Fin.last 3) = 1 :=
    (hM.row 4).trans (Matrix.one_apply_eq 4)
  have hsub : (M.submatrix Fin.succ Fin.succ).submatrix (Fin.last 3).succAbove
      (Fin.last 3).succAbove = thomBlock M := by
    rw [Fin.succAbove_last]
    rfl
  have h2 : (M.submatrix Fin.succ Fin.succ).det = (thomBlock M).det := by
    rw [Matrix.det_succ_row _ (Fin.last 3), Fin.sum_univ_castSucc]
    simp only [hrow, hsub, h44, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, mul_one]
    norm_num [Fin.val_last]
  exact h1.trans h2

/-- Elementary matrices have determinant `1`. -/
theorem det_eq_one_of_mem_elementaryGroup {A : (Matrix (Fin 3) (Fin 3) R)ˣ}
    (hA : A ∈ elementaryGroup (Fin 3) R) : (A : Matrix (Fin 3) (Fin 3) R).det = 1 := by
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (elementaryGroup_le_range_toGL hA)
  rw [← hg]
  exact g.2

end Coordinates

section Elements

variable {R : Type u} [CommRing R]

/-- The element of `G_0(R)` with Thom coordinates `(u, A, v, d)`. -/
def thomElem (u : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) (d : R)
    (h : A.det = 1) : thomG0 R :=
  ⟨⟨thomMat u A v d, by
      rw [det_eq_det_thomBlock (isThomShape_thomMat u A v d), thomBlock_thomMat]
      exact h⟩,
    (mem_thomG0 R).2 (isThomShape_thomMat u A v d)⟩

theorem thomElem_eq_thomElem {u u' : Fin 3 → R} {A A' : Matrix (Fin 3) (Fin 3) R}
    {v v' : Fin 3 → R} {d d' : R} {h : A.det = 1} {h' : A'.det = 1} (hu : u = u') (hA : A = A')
    (hv : v = v') (hd : d = d') : thomElem u A v d h = thomElem u' A' v' d' h' := by
  subst hu hA hv hd
  rfl

theorem thomElem_mul (u : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) (d : R)
    (h1 : A.det = 1) (u' : Fin 3 → R) (A' : Matrix (Fin 3) (Fin 3) R) (v' : Fin 3 → R) (d' : R)
    (h2 : A'.det = 1) :
    thomElem u A v d h1 * thomElem u' A' v' d' h2 =
      thomElem (u' + u ᵥ* A') (A * A') (A *ᵥ v' + v) (d' + u ⬝ᵥ v' + d)
        (by rw [Matrix.det_mul, h1, h2, one_mul]) := by
  apply Subtype.ext
  apply Subtype.ext
  exact thomMat_mul u A v d u' A' v' d'

theorem thomElem_one : thomElem (0 : Fin 3 → R) 1 0 0 Matrix.det_one = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact thomMat_zero_one

/-- The row elements `r(u)` of the Heisenberg kernel. -/
def thomRowE (u : Fin 3 → R) : thomG0 R := thomElem u 1 0 0 Matrix.det_one

/-- The column elements `c(v)` of the Heisenberg kernel. -/
def thomColE (v : Fin 3 → R) : thomG0 R := thomElem 0 1 v 0 Matrix.det_one

variable (R) in
/-- The middle block `G_0(R) →* SL_3(R)` (Thom, §2.1). -/
def thomBlockHom : thomG0 R →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun g := ⟨thomBlock g.1.1, (det_eq_det_thomBlock ((mem_thomG0 R).1 g.2)).symm.trans g.1.2⟩
  map_one' := by
    apply Subtype.ext
    show thomBlock (1 : Matrix (Fin 5) (Fin 5) R) = 1
    exact thomBlock_one
  map_mul' g g' := by
    apply Subtype.ext
    exact thomBlock_mul ((mem_thomG0 R).1 g.2) ((mem_thomG0 R).1 g'.2)

theorem thomBlockHom_surjective : Function.Surjective (thomBlockHom R) := fun A =>
  ⟨thomElem 0 A.1 0 0 A.2, Subtype.ext (thomBlock_thomMat 0 A.1 0 0)⟩

/-- Elements of the kernel of the block map have Thom coordinates `(u, 1, v, d)`. -/
theorem eq_thomElem_of_mem_ker {k : thomG0 R} (hk : k ∈ (thomBlockHom R).ker) :
    k = thomElem (fun b => k.1.1 0 (thomIdx b)) 1 (fun a => k.1.1 (thomIdx a) 4) (k.1.1 0 4)
      Matrix.det_one := by
  have hM : IsThomShape k.1.1 := (mem_thomG0 R).1 k.2
  have hB : thomBlock k.1.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
  apply Subtype.ext
  apply Subtype.ext
  show k.1.1 = thomMat (fun b => k.1.1 0 (thomIdx b)) 1 (fun a => k.1.1 (thomIdx a) 4) (k.1.1 0 4)
  exact (eq_thomMat hM).trans (by rw [hB])

theorem thomElem_split (u v : Fin 3 → R) (d : R) :
    thomElem u 1 v d Matrix.det_one =
      thomRowE u * thomColE v * thomElem 0 1 0 (d - u ⬝ᵥ v) Matrix.det_one := by
  unfold thomRowE thomColE
  rw [thomElem_mul, thomElem_mul]
  apply thomElem_eq_thomElem
  all_goals simp [Matrix.vecMul_one, Matrix.one_mulVec, Matrix.mulVec_zero, dotProduct_zero]

/-- The centre `e_15(c)` as a commutator of row and column elements. -/
theorem thomElem_corner (a w : Fin 3 → R) (c : R) (hc : a ⬝ᵥ w = c) :
    thomElem 0 1 0 c Matrix.det_one =
      thomRowE a * thomColE w * thomRowE (-a) * thomColE (-w) := by
  unfold thomRowE thomColE
  rw [thomElem_mul, thomElem_mul, thomElem_mul]
  apply thomElem_eq_thomElem
  all_goals simp [hc, Matrix.vecMul_one, Matrix.one_mulVec, Matrix.mulVec_zero, dotProduct_zero,
    zero_dotProduct]

/-- **Bounded generation of the Heisenberg kernel** (Thom, §2.1): every element of the kernel of
the block map is a product of three row elements and three column elements. -/
theorem thom_exists_prod_of_mem_ker {k : thomG0 R} (hk : k ∈ (thomBlockHom R).ker) :
    ∃ u v a w : Fin 3 → R,
      k = thomRowE u * thomColE v * thomRowE a * thomColE w * thomRowE (-a) * thomColE (-w) := by
  obtain ⟨u, v, d, hkeq⟩ : ∃ u v : Fin 3 → R, ∃ d : R, k = thomElem u 1 v d Matrix.det_one :=
    ⟨_, _, _, eq_thomElem_of_mem_ker hk⟩
  refine ⟨u, v, Pi.single 0 (d - u ⬝ᵥ v), Pi.single 0 1, ?_⟩
  rw [hkeq, thomElem_split u v d,
    thomElem_corner (Pi.single 0 (d - u ⬝ᵥ v)) (Pi.single 0 1) (d - u ⬝ᵥ v) (by simp)]
  simp only [mul_assoc]

end Elements

section Copies

variable {R : Type u} [CommRing R]
variable (φ : elementaryGroup (Fin 3) R →* MulAut (Multiplicative (Fin 3 → R)))

/-- Column copy of `R³ ⋊ EL_3(R)` in `G_0(R)`, as a function. -/
def thomColFun
    (g : SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) φ) :
    thomG0 R :=
  thomElem 0 ((g.right : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R)
    (Multiplicative.toAdd g.left) 0 (det_eq_one_of_mem_elementaryGroup g.right.2)

theorem thomColFun_one : thomColFun φ 1 = 1 := by
  unfold thomColFun
  refine Eq.trans ?_ thomElem_one
  apply thomElem_eq_thomElem <;> first | rfl | simp

theorem thomColFun_mul
    (hφ : ∀ (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)),
      φ A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n))
    (g g' : SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) φ) :
    thomColFun φ (g * g') = thomColFun φ g * thomColFun φ g' := by
  unfold thomColFun
  rw [thomElem_mul]
  apply thomElem_eq_thomElem
  · simp
  · first | rfl | simp
  · rw [SemidirectProduct.mul_left, toAdd_mul, hφ, toAdd_ofAdd]
    exact add_comm _ _
  · simp

/-- The column copy `(v, A) ↦ [[1,0,0],[0,A,v],[0,0,1]]`. -/
def thomColHom
    (hφ : ∀ (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)),
      φ A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n)) :
    SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) φ →* thomG0 R where
  toFun := thomColFun φ
  map_one' := thomColFun_one φ
  map_mul' := thomColFun_mul φ hφ

theorem thomColHom_inl
    (hφ : ∀ (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)),
      φ A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n))
    (n : Multiplicative (Fin 3 → R)) :
    thomColHom φ hφ (SemidirectProduct.inl n) = thomColE (Multiplicative.toAdd n) := by
  show thomColFun φ (SemidirectProduct.inl n) = thomColE (Multiplicative.toAdd n)
  unfold thomColFun thomColE
  apply thomElem_eq_thomElem <;> first | rfl | simp

/-- The dual block `(A⁻¹)ᵀ`. -/
def thomDual (A : elementaryGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  (((A⁻¹ : elementaryGroup (Fin 3) R) : (Matrix (Fin 3) (Fin 3) R)ˣ) :
    Matrix (Fin 3) (Fin 3) R)ᵀ

theorem det_thomDual (A : elementaryGroup (Fin 3) R) : (thomDual A).det = 1 := by
  unfold thomDual
  rw [Matrix.det_transpose]
  exact det_eq_one_of_mem_elementaryGroup (A⁻¹).2

theorem thomDual_one : thomDual (1 : elementaryGroup (Fin 3) R) = 1 := by
  unfold thomDual
  simp [Matrix.transpose_one]

theorem thomDual_mul (A B : elementaryGroup (Fin 3) R) :
    thomDual (A * B) = thomDual A * thomDual B := by
  unfold thomDual
  first
    | (rw [mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul]; done)
    | simp

theorem mulVec_vecMul_thomDual (A : elementaryGroup (Fin 3) R) (w : Fin 3 → R) :
    (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ w) ᵥ* thomDual A = w := by
  unfold thomDual
  first
    | (rw [Matrix.vecMul_transpose, Matrix.mulVec_mulVec, Subgroup.coe_inv, Units.inv_mul,
        Matrix.one_mulVec]; done)
    | simp [Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

/-- Row copy of `R³ ⋊ EL_3(R)` in `G_0(R)`, as a function. -/
def thomRowFun
    (g : SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) φ) :
    thomG0 R :=
  thomElem (Multiplicative.toAdd g.left ᵥ* thomDual g.right) (thomDual g.right) 0 0
    (det_thomDual g.right)

theorem thomRowFun_one : thomRowFun φ 1 = 1 := by
  unfold thomRowFun
  refine Eq.trans ?_ thomElem_one
  apply thomElem_eq_thomElem
  · simp [SemidirectProduct.one_left, SemidirectProduct.one_right, thomDual_one]
  · rw [SemidirectProduct.one_right, thomDual_one]
  · rfl
  · rfl

theorem thomRowFun_mul
    (hφ : ∀ (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)),
      φ A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n))
    (g g' : SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) φ) :
    thomRowFun φ (g * g') = thomRowFun φ g * thomRowFun φ g' := by
  unfold thomRowFun
  rw [thomElem_mul]
  apply thomElem_eq_thomElem
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, toAdd_mul, hφ, toAdd_ofAdd,
      thomDual_mul, ← Matrix.vecMul_vecMul, Matrix.add_vecMul, mulVec_vecMul_thomDual,
      Matrix.add_vecMul]
    exact add_comm _ _
  · rw [SemidirectProduct.mul_right, thomDual_mul]
  · simp
  · simp

/-- The row copy `(n, A) ↦ [[1,nᵀ(A⁻¹)ᵀ,0],[0,(A⁻¹)ᵀ,0],[0,0,1]]`. -/
def thomRowHom
    (hφ : ∀ (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)),
      φ A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n)) :
    SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) φ →* thomG0 R where
  toFun := thomRowFun φ
  map_one' := thomRowFun_one φ
  map_mul' := thomRowFun_mul φ hφ

theorem thomRowHom_inl
    (hφ : ∀ (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)),
      φ A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n))
    (n : Multiplicative (Fin 3 → R)) :
    thomRowHom φ hφ (SemidirectProduct.inl n) = thomRowE (Multiplicative.toAdd n) := by
  show thomRowFun φ (SemidirectProduct.inl n) = thomRowE (Multiplicative.toAdd n)
  unfold thomRowFun thomRowE
  apply thomElem_eq_thomElem
  · rw [SemidirectProduct.left_inl, SemidirectProduct.right_inl, thomDual_one, Matrix.vecMul_one]
  · rw [SemidirectProduct.right_inl, thomDual_one]
  · rfl
  · rfl

end Copies

section Relative

variable {R : Type u} [CommRing R]

/-- Displacement is subadditive along products. -/
theorem thom_norm_map_mul_sub_le {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g h : G) (x : E) :
    ‖ρ (g * h) x - x‖ ≤ ‖ρ g x - x‖ + ‖ρ h x - x‖ := by
  have hmul : ρ (g * h) x = ρ g (ρ h x) :=
    congrArg (fun T : E ≃ₗᵢ[ℝ] E ↦ T x) (map_mul ρ g h)
  have hsplit : ρ (g * h) x - x = ρ g (ρ h x - x) + (ρ g x - x) := by
    rw [hmul, map_sub]
    abel
  rw [hsplit]
  calc ‖ρ g (ρ h x - x) + (ρ g x - x)‖ ≤ ‖ρ g (ρ h x - x)‖ + ‖ρ g x - x‖ := norm_add_le _ _
    _ = ‖ρ h x - x‖ + ‖ρ g x - x‖ := by rw [LinearIsometryEquiv.norm_map]
    _ = ‖ρ g x - x‖ + ‖ρ h x - x‖ := add_comm _ _

/-- **Relative property (T) for `(G_0(R), N)`** (Thom, GGD 4 (2010), §2.1, proof of Lemma 2.1):
relative property (T) for `(R³ ⋊ EL_3(R), R³)`, with the linear action, gives relative property
(T) for the Heisenberg kernel `N` of the block map `G_0(R) → SL_3(R)`. -/
theorem hasRelativePropertyT_thomG0_ker
    (φ : elementaryGroup (Fin 3) R →* MulAut (Multiplicative (Fin 3 → R)))
    (hφ : ∀ (A : elementaryGroup (Fin 3) R) (n : Multiplicative (Fin 3 → R)),
      φ A n = Multiplicative.ofAdd
        (((A : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) *ᵥ Multiplicative.toAdd n))
    (hrel : HasRelativePropertyT.{u, v}
      (SemidirectProduct (Multiplicative (Fin 3 → R)) (elementaryGroup (Fin 3) R) φ)
      (SemidirectProductKazhdan.normalCopy φ)) :
    HasRelativePropertyT.{u, v} (thomG0 R) (thomBlockHom R).ker := by
  classical
  obtain ⟨Q, ε, hQ⟩ := hrel
  have hε : 0 < ε := hQ.1
  refine ⟨Q.image (thomColHom φ hφ) ∪ Q.image (thomRowHom φ hφ), ε / 24, ?_⟩
  refine isRelativeKazhdanPair_of_displacement _ _ (by linarith) ?_
  intro E _ _ _ ρ x hx hnear
  have hcolb : ∀ w : Fin 3 → R, ‖ρ (thomColE w) x - x‖ ≤ 1 / 12 := by
    intro w
    have h := hQ.mul_norm_displacement_le_of_hom (thomColHom φ hφ) ρ x (δ := ε / 24)
      (by linarith)
      (fun q hq => (hnear _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))).le)
      (SemidirectProductKazhdan.inl_mem_normalCopy (Multiplicative.ofAdd w))
    rw [thomColHom_inl, toAdd_ofAdd] at h
    refine le_of_mul_le_mul_left ?_ hε
    linarith
  have hrowb : ∀ w : Fin 3 → R, ‖ρ (thomRowE w) x - x‖ ≤ 1 / 12 := by
    intro w
    have h := hQ.mul_norm_displacement_le_of_hom (thomRowHom φ hφ) ρ x (δ := ε / 24)
      (by linarith)
      (fun q hq => (hnear _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))).le)
      (SemidirectProductKazhdan.inl_mem_normalCopy (Multiplicative.ofAdd w))
    rw [thomRowHom_inl, toAdd_ofAdd] at h
    refine le_of_mul_le_mul_left ?_ hε
    linarith
  intro k hk
  obtain ⟨a, b, c, w, rfl⟩ := thom_exists_prod_of_mem_ker hk
  have h1 := thom_norm_map_mul_sub_le ρ
    (thomRowE a * thomColE b * thomRowE c * thomColE w * thomRowE (-c)) (thomColE (-w)) x
  have h2 := thom_norm_map_mul_sub_le ρ
    (thomRowE a * thomColE b * thomRowE c * thomColE w) (thomRowE (-c)) x
  have h3 := thom_norm_map_mul_sub_le ρ (thomRowE a * thomColE b * thomRowE c) (thomColE w) x
  have h4 := thom_norm_map_mul_sub_le ρ (thomRowE a * thomColE b) (thomRowE c) x
  have h5 := thom_norm_map_mul_sub_le ρ (thomRowE a) (thomColE b) x
  linarith [hrowb a, hcolb b, hrowb c, hcolb w, hrowb (-c), hcolb (-w)]

end Relative

end

#audit_axioms hasRelativePropertyT_thomG0_ker

end GroupApproximation.Full.A2ThomT
