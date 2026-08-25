import Mathlib.GroupTheory.Subgroup.Simple
import GroupApproximation.Leavitt.ElementaryNormalGeneration

/-!
# Foundational root extraction for simplicity of `EL_ι(R)`

Proposition `prop:simple` of `non_mf_groups_exist.tex` asserts that
`H = EL₁₂(L_{𝔽₂}(1,2))` is simple.  The manuscript gets that from Preusser's
normal-subgroup theorem (the sandwich classification
`EL_n(R, I) ≤ N ≤ C_n(R, I)`) together with `Z(R) = 𝔽₂`.  The Preusser
upper-sandwich theorem itself is not formalized in this repository.  The
coefficient-ring centre and its central units are formalized separately in
`BinaryLeavittSimple`, while `DiagonalNormalExtraction` closes the manuscript's
exact simplicity claim by a direct exhaustive root-extraction argument that
does not require the upper sandwich.

What *is* in the repository is the strongest possible statement **after** a
root has been detected: `elementaryGroup_normal_eq_top_of_elGen_mem`
(`Leavitt.ElementaryNormalGeneration`) says that a normal subgroup containing a
single elementary root `e_{ij}(x)` whose coefficient admits a unit sandwich
`a * x * b = 1` is already everything, and
`BinaryLeavitt.exists_mul_mul_eq_one` (`Leavitt.LeavittSimplicity`) supplies
that sandwich for *every* nonzero coefficient of `L_k(1,2)`.  So simplicity of
`H` is exactly the **root-detection** statement

  `(P)`  every nontrivial normal subgroup of `EL_ι(R)` contains a nonzero
         elementary root.

This file supplies concrete post-detection routes and isolates `(P)` as an
explicit generic hypothesis.  The separate Leavitt-family specialization in
`DiagonalNormalExtraction` proves that hypothesis and applies the reduction
below unconditionally.

## What is proved here

* **Thin-matrix extraction** (`normal_eq_top_of_colMatrix_mem`).  If a normal
  subgroup `N` contains a matrix that agrees with the identity off a single
  column and has a nonzero entry in that column away from the diagonal, then
  `N = ⊤`.

  The proof is one conjugation and one multiplication.  A matrix
  `1 + colMatrix q y` is inverted *inside* the column-supported family
  (`exists_elMat_inv_colMatrix`), and conjugating it by `e_{ij}(b)` with `i ≠ q` shifts the
  column by `b * y j` in slot `i` while fixing slot `q`; multiplying the
  conjugate by the original inverse cancels everything except the shift,
  leaving the honest root `e_{iq}((b * y j) * (1 + y' q))` with `1 + y' q` a
  unit (`exists_elGen_mem_of_colMatrix_mem`).

* **Double-commutator reduction** (`exists_colMatrix_mem_of_mem`,
  `normal_eq_top_of_double_commutator`).  Under explicit index, vanishing and
  nonvanishing hypotheses, the double commutator of an arbitrary normal-
  subgroup element with two elementary roots is a nontrivial column-supported
  perturbation, so the preceding extraction theorem applies.

* **The scalar exceptional branch** (`center_elementaryGroup_eq_bot`).
  Commuting with all elementary roots forces an elementary-group element to be
  a scalar central unit.  Thus the elementary-group centre is trivial whenever
  the coefficient ring has no nontrivial central units.

* **The final conditional reduction** (`RootDetection`,
  `isSimpleGroup_of_rootDetection`).  Once every nontrivial normal subgroup is
  known to contain a nonzero elementary root, the existing normal-generation
  theorem gives `IsSimpleGroup`.

## Scope of this foundational file

The generic `RootDetection` definition and reduction below remain useful on
their own: the double-commutator theorem in this file asks the caller to choose
indices and coefficients satisfying explicit vanishing and nonvanishing
conditions.  For a Leavitt family, those choices and the remaining case split
are supplied in `ElementaryTransvectionExtraction` and
`DiagonalNormalExtraction`.  Thus the general Preusser upper sandwich remains
an optional, separately recorded route; it is not a missing premise of the
unconditional manuscript theorem.
-/

namespace GroupApproximation
namespace ElementarySimplicity

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ## Single-entry products

The two entry formulas below are the same computations as
`GeneralScheme.mul_single_apply` and `GeneralScheme.single_mul_apply`; they are
repeated here so that this file depends only on `ElementaryNormalGeneration`.
-/

theorem mul_single_apply (M : Matrix ι ι R) (i j : ι) (a : R) (r c : ι) :
    (M * Matrix.single i j a) r c = if c = j then M r i * a else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hcj : c = j
  · rw [if_pos hcj, Finset.sum_eq_single i]
    · rw [Matrix.single_apply, if_pos ⟨rfl, hcj.symm⟩]
    · intro k _ hki
      rw [Matrix.single_apply, if_neg fun h => hki h.1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [if_neg hcj]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hcj h.2.symm, mul_zero]

theorem single_mul_apply (i j : ι) (a : R) (M : Matrix ι ι R) (r c : ι) :
    (Matrix.single i j a * M) r c = if r = i then a * M j c else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hri : r = i
  · rw [if_pos hri, Finset.sum_eq_single j]
    · rw [Matrix.single_apply, if_pos ⟨hri.symm, rfl⟩]
    · intro k _ hkj
      rw [Matrix.single_apply, if_neg fun h => hkj h.2.symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · rw [if_neg hri]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hri h.1.symm, zero_mul]

theorem sum_ite_right (j : ι) (f : ι → R) :
    ∑ z, (if z = j then f z else 0) = f j := by
  simp

/-! ## Row- and column-supported matrices -/

/-- The matrix supported on row `p`, whose `p`-th row is `w`. -/
def rowMatrix (p : ι) (w : ι → R) : Matrix ι ι R :=
  Matrix.of fun x y => if x = p then w y else 0

/-- The matrix supported on column `q`, whose `q`-th column is `y`. -/
def colMatrix (q : ι) (y : ι → R) : Matrix ι ι R :=
  Matrix.of fun x z => if z = q then y x else 0

omit [Fintype ι] in
@[simp] theorem rowMatrix_apply (p : ι) (w : ι → R) (x y : ι) :
    rowMatrix p w x y = if x = p then w y else 0 := rfl

omit [Fintype ι] in
@[simp] theorem colMatrix_apply (q : ι) (y : ι → R) (x z : ι) :
    colMatrix q y x z = if z = q then y x else 0 := rfl

omit [Fintype ι] in
theorem rowMatrix_eq_zero (p : ι) (w : ι → R) (hw : ∀ y, w y = 0) :
    rowMatrix p w = 0 := by
  ext x y
  simp only [rowMatrix_apply, Matrix.zero_apply, hw, ite_self]

omit [Fintype ι] in
theorem colMatrix_eq_zero (q : ι) (y : ι → R) (hy : ∀ x, y x = 0) :
    colMatrix q y = 0 := by
  ext x z
  simp only [colMatrix_apply, Matrix.zero_apply, hy, ite_self]

omit [Fintype ι] in
/-- A row-supported matrix is determined by its row. -/
theorem rowMatrix_row (p : ι) (w : ι → R) (y : ι) : rowMatrix p w p y = w y := by
  simp [rowMatrix_apply]

omit [Fintype ι] in
/-- A column-supported matrix is determined by its column. -/
theorem colMatrix_col (q : ι) (y : ι → R) (x : ι) : colMatrix q y x q = y x := by
  simp [colMatrix_apply]

omit [Fintype ι] in
theorem rowMatrix_add (p : ι) (w w' : ι → R) :
    rowMatrix p w + rowMatrix p w' = rowMatrix p (fun y => w y + w' y) := by
  ext x y
  simp only [Matrix.add_apply, rowMatrix_apply]
  by_cases hx : x = p
  · simp only [if_pos hx]
  · simp only [if_neg hx, add_zero]

omit [Fintype ι] in
theorem colMatrix_add (q : ι) (y y' : ι → R) :
    colMatrix q y + colMatrix q y' = colMatrix q (fun x => y x + y' x) := by
  ext x z
  simp only [Matrix.add_apply, colMatrix_apply]
  by_cases hz : z = q
  · simp only [if_pos hz]
  · simp only [if_neg hz, add_zero]

omit [Fintype ι] in
theorem colMatrix_neg (q : ι) (y : ι → R) :
    -colMatrix q y = colMatrix q (fun x => -y x) := by
  ext x z
  simp only [Matrix.neg_apply, colMatrix_apply]
  by_cases hz : z = q
  · simp only [if_pos hz]
  · simp only [if_neg hz, neg_zero]

omit [Fintype ι] in
/-- A single entry, read as a row-supported matrix. -/
theorem single_eq_rowMatrix (p j : ι) (c : R) :
    Matrix.single p j c = rowMatrix p (fun y => if y = j then c else 0) := by
  ext x y
  simp only [Matrix.single_apply, rowMatrix_apply]
  by_cases hx : x = p
  · rw [if_pos hx]
    by_cases hy : y = j
    · rw [if_pos hy, if_pos ⟨hx.symm, hy.symm⟩]
    · rw [if_neg hy, if_neg (fun h : p = x ∧ j = y => hy h.2.symm)]
  · rw [if_neg hx, if_neg (fun h : p = x ∧ j = y => hx h.1.symm)]

omit [Fintype ι] in
/-- A single entry, read as a column-supported matrix. -/
theorem single_eq_colMatrix (i q : ι) (c : R) :
    Matrix.single i q c = colMatrix q (fun x => if x = i then c else 0) := by
  ext x z
  simp only [Matrix.single_apply, colMatrix_apply]
  by_cases hz : z = q
  · rw [if_pos hz]
    by_cases hx : x = i
    · rw [if_pos hx, if_pos ⟨hx.symm, hz.symm⟩]
    · rw [if_neg hx, if_neg (fun h : i = x ∧ q = z => hx h.1.symm)]
  · rw [if_neg hz, if_neg (fun h : i = x ∧ q = z => hz h.2.symm)]

omit [Fintype ι] in
theorem single_zero_coeff (i j : ι) : Matrix.single i j (0 : R) = 0 := by
  ext x y
  simp only [Matrix.single_apply, Matrix.zero_apply, ite_self]

/-! ### Products -/

/-- Left multiplication by a single entry produces a row-supported matrix. -/
theorem single_mul_eq (i j : ι) (a : R) (M : Matrix ι ι R) :
    Matrix.single i j a * M = rowMatrix i (fun v => a * M j v) := by
  ext x y
  simp only [single_mul_apply, rowMatrix_apply]

/-- Right multiplication by a single entry produces a column-supported
matrix. -/
theorem mul_single_eq (M : Matrix ι ι R) (i j : ι) (a : R) :
    M * Matrix.single i j a = colMatrix j (fun x => M x i * a) := by
  ext x z
  simp only [mul_single_apply, colMatrix_apply]

/-- A row-supported matrix times a single entry is again a single entry. -/
theorem rowMatrix_mul_single (p : ι) (w : ι → R) (k l : ι) (a : R) :
    rowMatrix p w * Matrix.single k l a = Matrix.single p l (w k * a) := by
  ext x z
  simp only [mul_single_apply, Matrix.single_apply, rowMatrix_apply]
  by_cases hx : x = p
  · by_cases hz : z = l
    · rw [if_pos hz, if_pos hx, if_pos ⟨hx.symm, hz.symm⟩]
    · rw [if_neg hz, if_neg (fun h : p = x ∧ l = z => hz h.2.symm)]
  · by_cases hz : z = l
    · rw [if_pos hz, if_neg hx,
        if_neg (fun h : p = x ∧ l = z => hx h.1.symm), zero_mul]
    · rw [if_neg hz, if_neg (fun h : p = x ∧ l = z => hz h.2.symm)]

/-- A single entry times a column-supported matrix is again a single entry. -/
theorem single_mul_colMatrix (i j : ι) (a : R) (q : ι) (y : ι → R) :
    Matrix.single i j a * colMatrix q y = Matrix.single i q (a * y j) := by
  ext x z
  simp only [single_mul_apply, Matrix.single_apply, colMatrix_apply]
  by_cases hx : x = i
  · by_cases hz : z = q
    · rw [if_pos hx, if_pos hz, if_pos ⟨hx.symm, hz.symm⟩]
    · rw [if_neg hz, if_neg (fun h : i = x ∧ q = z => hz h.2.symm),
        if_pos hx, mul_zero]
  · rw [if_neg hx, if_neg (fun h : i = x ∧ q = z => hx h.1.symm)]

/-- A column-supported matrix times a single entry whose row index misses the
column vanishes. -/
theorem colMatrix_mul_single_of_ne (q : ι) (y : ι → R) (i j : ι) (a : R)
    (hiq : i ≠ q) : colMatrix q y * Matrix.single i j a = 0 := by
  ext x z
  simp only [mul_single_apply, colMatrix_apply, Matrix.zero_apply]
  by_cases hz : z = j
  · rw [if_pos hz, if_neg hiq, zero_mul]
  · rw [if_neg hz]

/-- A single entry whose column index misses the row times a row-supported
matrix vanishes. -/
theorem single_mul_rowMatrix_of_ne (i j : ι) (a : R) (p : ι) (w : ι → R)
    (hjp : j ≠ p) : Matrix.single i j a * rowMatrix p w = 0 := by
  ext x y
  simp only [single_mul_apply, rowMatrix_apply, Matrix.zero_apply]
  by_cases hx : x = i
  · rw [if_pos hx, if_neg hjp, mul_zero]
  · rw [if_neg hx]

/-- Any matrix times a column-supported matrix is column supported. -/
theorem mul_colMatrix (M : Matrix ι ι R) (q : ι) (y : ι → R) :
    M * colMatrix q y = colMatrix q (fun x => ∑ t, M x t * y t) := by
  ext x z
  simp only [Matrix.mul_apply, colMatrix_apply]
  by_cases hz : z = q
  · simp only [if_pos hz]
  · simp only [if_neg hz, mul_zero, Finset.sum_const_zero]

/-- Any row-supported matrix times a matrix is row supported. -/
theorem rowMatrix_mul (p : ι) (w : ι → R) (M : Matrix ι ι R) :
    rowMatrix p w * M = rowMatrix p (fun y => ∑ t, w t * M t y) := by
  ext x y
  simp only [Matrix.mul_apply, rowMatrix_apply]
  by_cases hx : x = p
  · simp only [if_pos hx]
  · simp only [if_neg hx, zero_mul, Finset.sum_const_zero]

/-- The column-supported family is closed under multiplication. -/
theorem colMatrix_mul_colMatrix (q : ι) (y y' : ι → R) :
    colMatrix q y * colMatrix q y' = colMatrix q (fun x => y x * y' q) := by
  rw [mul_colMatrix]
  congr 1
  funext x
  simp only [colMatrix_apply, ite_mul, zero_mul]
  exact sum_ite_right q (fun t => y x * y' t)

/-- The row-supported family is closed under multiplication. -/
theorem rowMatrix_mul_rowMatrix (p : ι) (w w' : ι → R) :
    rowMatrix p w * rowMatrix p w' = rowMatrix p (fun y => w p * w' y) := by
  rw [rowMatrix_mul]
  congr 1
  funext y
  simp only [rowMatrix_apply, mul_ite, mul_zero]
  exact sum_ite_right p (fun t => w t * w' y)

/-- Products of column-supported unipotents. -/
theorem one_add_colMatrix_mul (q : ι) (y y' : ι → R) :
    (1 + colMatrix q y) * (1 + colMatrix q y') =
      1 + colMatrix q (fun x => y x + y' x + y x * y' q) := by
  have hexpand : (1 + colMatrix q y) * (1 + colMatrix q y') =
      1 + (colMatrix q y + colMatrix q y' + colMatrix q y * colMatrix q y') := by
    noncomm_ring
  rw [hexpand, colMatrix_mul_colMatrix]
  congr 1
  ext x z
  simp only [Matrix.add_apply, colMatrix_apply]
  by_cases hz : z = q
  · simp only [if_pos hz]
  · simp only [if_neg hz, add_zero]

/-- Products of row-supported unipotents. -/
theorem one_add_rowMatrix_mul (p : ι) (w w' : ι → R) :
    (1 + rowMatrix p w) * (1 + rowMatrix p w') =
      1 + rowMatrix p (fun y => w y + w' y + w p * w' y) := by
  have hexpand : (1 + rowMatrix p w) * (1 + rowMatrix p w') =
      1 + (rowMatrix p w + rowMatrix p w' + rowMatrix p w * rowMatrix p w') := by
    noncomm_ring
  rw [hexpand, rowMatrix_mul_rowMatrix]
  congr 1
  ext x y
  simp only [Matrix.add_apply, rowMatrix_apply]
  by_cases hx : x = p
  · simp only [if_pos hx]
  · simp only [if_neg hx, add_zero]


/-! ## Conjugating a column-supported unipotent -/

/-- Conjugating `1 + colMatrix q y` by `e_{ij}(b)` with `i ≠ q` adds `b * y j`
to slot `i` of the column and changes nothing else. -/
theorem conj_one_add_colMatrix (q : ι) (y : ι → R) (i j : ι) (hij : i ≠ j)
    (hiq : i ≠ q) (b : R) :
    (1 + Matrix.single i j b) * (1 + colMatrix q y) *
        (1 - Matrix.single i j b) =
      1 + colMatrix q (fun x => y x + if x = i then b * y j else 0) := by
  have hSS : Matrix.single i j b * Matrix.single i j b = 0 :=
    single_mul_self_eq_zero i j hij b
  have hCS : colMatrix q y * Matrix.single i j b = 0 :=
    colMatrix_mul_single_of_ne q y i j b hiq
  have hSCS : Matrix.single i j b * colMatrix q y * Matrix.single i j b = 0 := by
    rw [mul_assoc, hCS, mul_zero]
  have hkey : (1 + Matrix.single i j b) * (1 + colMatrix q y) *
      (1 - Matrix.single i j b) =
      1 + (colMatrix q y + Matrix.single i j b * colMatrix q y) := by
    noncomm_ring [hSS, hCS, hSCS]
  rw [hkey, single_mul_colMatrix, single_eq_colMatrix, colMatrix_add]

/-! ## The square-zero commutator identity -/

/-- For square-zero `X` and `Y` with `Y * X = 0`, the group commutator of
`1 + X` and `1 + Y` is `1 + X * Y`. -/
theorem commutator_of_mul_eq_zero {A : Type*} [Ring A] {X Y : A}
    (hX : X * X = 0) (hY : Y * Y = 0) (hYX : Y * X = 0) :
    (1 + X) * (1 + Y) * (1 - X) * (1 - Y) = 1 + X * Y := by
  have h1 : (1 + Y) * (1 - X) = 1 - X + Y := by noncomm_ring [hYX]
  have h2 : (1 + X) * (1 - X + Y) = 1 + Y + X * Y := by noncomm_ring [hX]
  have hXYY : X * Y * Y = 0 := by rw [mul_assoc, hY, mul_zero]
  have h3 : (1 + Y + X * Y) * (1 - Y) = 1 + X * Y := by noncomm_ring [hY, hXYY]
  rw [mul_assoc (1 + X) (1 + Y) (1 - X), h1, h2, h3]

/-- Commuting the second entry past an inverse: if `t` and `z` commute then the
commutator of `A * t⁻¹` with `z` is the commutator of `A` with `z`. -/
theorem conj_commutator_eq_of_commute {G : Type*} [Group G] (A t z : G)
    (h : Commute t z) :
    A * t⁻¹ * z * (A * t⁻¹)⁻¹ * z⁻¹ = A * z * A⁻¹ * z⁻¹ := by
  have ht : t⁻¹ * z * t = z := by
    rw [(h.inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]
  calc A * t⁻¹ * z * (A * t⁻¹)⁻¹ * z⁻¹
      = A * (t⁻¹ * z * t) * A⁻¹ * z⁻¹ := by group
    _ = A * z * A⁻¹ * z⁻¹ := by rw [ht]

/-! ## The underlying matrix of an element of `EL_ι(R)` -/

/-- The underlying matrix of an element of the elementary group. -/
def elMat (g : elementaryGroup ι R) : Matrix ι ι R :=
  ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R)

theorem elMat_mul (g h : elementaryGroup ι R) :
    elMat (g * h) = elMat g * elMat h := rfl

theorem elMat_mul_inv (g : elementaryGroup ι R) : elMat g * elMat (g⁻¹) = 1 :=
  Units.mul_inv _

theorem elMat_inv_mul (g : elementaryGroup ι R) : elMat (g⁻¹) * elMat g = 1 :=
  Units.inv_mul _

theorem elMat_elGen (i j : ι) (hij : i ≠ j) (a : R) :
    elMat (elGen i j hij a) = 1 + Matrix.single i j a := rfl

theorem elMat_elGen_inv (i j : ι) (hij : i ≠ j) (a : R) :
    elMat ((elGen i j hij a)⁻¹) = 1 - Matrix.single i j a := rfl

theorem elMat_injective :
    Function.Injective (elMat : elementaryGroup ι R → Matrix ι ι R) := by
  intro g h hgh
  exact Subtype.ext (Units.ext hgh)

/-! ## Root extraction from a column-supported element -/

/-- The inverse of a column-supported unipotent is column supported. -/
theorem exists_elMat_inv_colMatrix {M : elementaryGroup ι R} {q : ι}
    {y : ι → R} (hval : elMat M = 1 + colMatrix q y) :
    ∃ y' : ι → R, elMat (M⁻¹) = 1 + colMatrix q y' := by
  refine ⟨fun x => -(∑ t, elMat (M⁻¹) x t * y t), ?_⟩
  have hinv : elMat (M⁻¹) * elMat M = 1 := elMat_inv_mul M
  rw [hval, mul_add, mul_one, mul_colMatrix] at hinv
  rw [← colMatrix_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
  exact hinv

/-- **Root extraction.**  A normal subgroup containing a matrix that agrees with
the identity off the single column `q` contains an honest elementary root at
`(i, q)`, whose coefficient is a unit multiple of `b * y j`. -/
theorem exists_elGen_mem_of_colMatrix_mem
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal]
    {M : elementaryGroup ι R} (hM : M ∈ N) {q : ι} {y : ι → R}
    (hval : elMat M = 1 + colMatrix q y)
    {i j : ι} (hij : i ≠ j) (hiq : i ≠ q) (b : R) :
    ∃ c : R, elGen i q hiq c ∈ N ∧ (b * y j ≠ 0 → c ≠ 0) := by
  obtain ⟨y', hy'⟩ := exists_elMat_inv_colMatrix hval
  have hzero : ∀ x : ι, y x + y' x + y x * y' q = 0 := by
    have hprod : elMat M * elMat (M⁻¹) = 1 := elMat_mul_inv M
    rw [hval, hy', one_add_colMatrix_mul] at hprod
    intro x
    have hx := congrFun (congrFun hprod x) q
    rw [Matrix.add_apply, colMatrix_col] at hx
    have hx' : (1 : Matrix ι ι R) x q + (y x + y' x + y x * y' q)
        = (1 : Matrix ι ι R) x q + 0 := by
      rw [add_zero]
      exact hx
    exact add_left_cancel hx'
  have hzero' : ∀ x : ι, y' x + y x + y' x * y q = 0 := by
    have hprod : elMat (M⁻¹) * elMat M = 1 := elMat_inv_mul M
    rw [hval, hy', one_add_colMatrix_mul] at hprod
    intro x
    have hx := congrFun (congrFun hprod x) q
    rw [Matrix.add_apply, colMatrix_col] at hx
    have hx' : (1 : Matrix ι ι R) x q + (y' x + y x + y' x * y q)
        = (1 : Matrix ι ι R) x q + 0 := by
      rw [add_zero]
      exact hx
    exact add_left_cancel hx'
  refine ⟨b * y j * (1 + y' q), ?_, ?_⟩
  · have hmem : elGen i j hij b * M * (elGen i j hij b)⁻¹ * (M⁻¹) ∈ N :=
      N.mul_mem (hN.conj_mem M hM (elGen i j hij b)) (N.inv_mem hM)
    have hsplit : elMat (elGen i j hij b * M * (elGen i j hij b)⁻¹ * (M⁻¹))
        = elMat (elGen i j hij b) * elMat M * elMat ((elGen i j hij b)⁻¹) *
          elMat (M⁻¹) := rfl
    have hfun : (fun x : ι =>
          (y x + if x = i then b * y j else 0) + y' x +
            (y x + if x = i then b * y j else 0) * y' q)
        = fun x : ι => if x = i then b * y j * (1 + y' q) else 0 := by
      funext x
      by_cases hx : x = i
      · rw [if_pos hx, if_pos hx]
        calc y x + b * y j + y' x + (y x + b * y j) * y' q
            = y x + y' x + y x * y' q + b * y j * (1 + y' q) := by noncomm_ring
          _ = 0 + b * y j * (1 + y' q) := by rw [hzero x]
          _ = b * y j * (1 + y' q) := zero_add _
      · rw [if_neg hx, if_neg hx, add_zero]
        exact hzero x
    have hEq : elGen i j hij b * M * (elGen i j hij b)⁻¹ * (M⁻¹)
        = elGen i q hiq (b * y j * (1 + y' q)) := by
      apply elMat_injective
      rw [hsplit, elMat_elGen, elMat_elGen_inv, elMat_elGen, hval, hy',
        conj_one_add_colMatrix q y i j hij hiq b, one_add_colMatrix_mul, hfun,
        single_eq_colMatrix]
    rwa [hEq] at hmem
  · intro hbj hc
    apply hbj
    have hunit : (1 + y' q) * (1 + y q) = 1 := by
      calc (1 + y' q) * (1 + y q) = 1 + (y' q + y q + y' q * y q) := by
            noncomm_ring
        _ = 1 + 0 := by rw [hzero' q]
        _ = 1 := add_zero 1
    calc b * y j = b * y j * ((1 + y' q) * (1 + y q)) := by rw [hunit, mul_one]
      _ = b * y j * (1 + y' q) * (1 + y q) := by noncomm_ring
      _ = 0 * (1 + y q) := by rw [hc]
      _ = 0 := zero_mul _

/-- **Thin-matrix extraction, in the form the simplicity argument needs.**  A
normal subgroup of `EL_ι(R)` containing a matrix that agrees with the identity
off a single column, and whose column has a nonzero entry, is everything --
provided nonzero coefficients admit unit sandwiches. -/
theorem normal_eq_top_of_colMatrix_mem
    (hcard : 3 ≤ Fintype.card ι)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {M : elementaryGroup ι R} (hM : M ∈ N) {q : ι} {y : ι → R}
    (hval : elMat M = 1 + colMatrix q y)
    {j : ι} (hyj : y j ≠ 0) :
    N = ⊤ := by
  obtain ⟨i, hij, hiq⟩ := exists_third_index hcard j q
  obtain ⟨c, hmem, hne⟩ :=
    exists_elGen_mem_of_colMatrix_mem N hM hval hij hiq 1
  have hc : c ≠ 0 := hne (by rwa [one_mul])
  exact elementaryGroup_normal_eq_top_of_elGen_mem hcard N hiq hmem (hdiv c hc)


/-! ## Thin matrices out of an arbitrary group element -/

/-- **The double commutator.**  For `g` in a normal subgroup `N` and a
*commuting* pair of elementary matrices `t = e_{kl}(a)` and `z = e_{pq}(b)`
(that is `l ≠ p` and `q ≠ k`), the double commutator `⁅⁅g, t⁆, z⁆` lies in `N`;
and when the scalar obstruction `b * g_{qk} * a` vanishes it is a matrix
agreeing with the identity off the single column `q`, whose column is
`x ↦ g_{xk} * (a * (g⁻¹)_{lp} * b)`. -/
theorem exists_colMatrix_mem_of_mem
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) {k l p q : ι}
    (hkl : k ≠ l) (hpq : p ≠ q) (hlp : l ≠ p) (hqk : q ≠ k) (a b : R)
    (hobs : b * elMat g q k * a = 0) :
    ∃ M : elementaryGroup ι R, M ∈ N ∧
      elMat M =
        1 + colMatrix q (fun x => elMat g x k * (a * (elMat (g⁻¹) l p * b))) := by
  refine ⟨g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹ * elGen p q hpq b *
      (g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹)⁻¹ *
      (elGen p q hpq b)⁻¹, ?_, ?_⟩
  · have hc : g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹ ∈ N := by
      have h1 : elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹ ∈ N :=
        hN.conj_mem (g⁻¹) (N.inv_mem hg) (elGen k l hkl a)
      have h2 : g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹
          = g * (elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹) := by
        simp only [mul_assoc]
      rw [h2]
      exact N.mul_mem hg h1
    have h3 : g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹ * elGen p q hpq b *
          (g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹)⁻¹ *
          (elGen p q hpq b)⁻¹
        = (g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹) *
          (elGen p q hpq b *
            (g * elGen k l hkl a * g⁻¹ * (elGen k l hkl a)⁻¹)⁻¹ *
            (elGen p q hpq b)⁻¹) := by
      simp only [mul_assoc]
    rw [h3]
    exact N.mul_mem hc (hN.conj_mem _ (N.inv_mem hc) (elGen p q hpq b))
  · have hcomm : Commute (elGen k l hkl a) (elGen p q hpq b) :=
      elementaryRoot_commute_of_ne k l p q hkl hpq hlp hqk a b
    rw [conj_commutator_eq_of_commute (g * elGen k l hkl a * g⁻¹)
      (elGen k l hkl a) (elGen p q hpq b) hcomm]
    have hgg : elMat (g⁻¹) * elMat g = 1 := elMat_inv_mul g
    have hSS : Matrix.single k l a * Matrix.single k l a = 0 :=
      single_mul_self_eq_zero k l hkl a
    have hYY : Matrix.single p q b * Matrix.single p q b = 0 :=
      single_mul_self_eq_zero p q hpq b
    have hXX : elMat g * Matrix.single k l a * elMat (g⁻¹) *
        (elMat g * Matrix.single k l a * elMat (g⁻¹)) = 0 := by
      calc elMat g * Matrix.single k l a * elMat (g⁻¹) *
            (elMat g * Matrix.single k l a * elMat (g⁻¹))
          = elMat g * Matrix.single k l a * (elMat (g⁻¹) * elMat g) *
              Matrix.single k l a * elMat (g⁻¹) := by noncomm_ring
        _ = elMat g * Matrix.single k l a * 1 * Matrix.single k l a *
              elMat (g⁻¹) := by rw [hgg]
        _ = elMat g * (Matrix.single k l a * Matrix.single k l a) *
              elMat (g⁻¹) := by noncomm_ring
        _ = 0 := by rw [hSS, mul_zero, zero_mul]
    have hYX : Matrix.single p q b *
        (elMat g * Matrix.single k l a * elMat (g⁻¹)) = 0 := by
      calc Matrix.single p q b * (elMat g * Matrix.single k l a * elMat (g⁻¹))
          = Matrix.single p q b * elMat g * Matrix.single k l a *
              elMat (g⁻¹) := by noncomm_ring
        _ = rowMatrix p (fun v => b * elMat g q v) * Matrix.single k l a *
              elMat (g⁻¹) := by rw [single_mul_eq]
        _ = Matrix.single p l (b * elMat g q k * a) * elMat (g⁻¹) := by
              rw [rowMatrix_mul_single]
        _ = 0 := by rw [hobs, single_zero_coeff, zero_mul]
    have hXY : elMat g * Matrix.single k l a * elMat (g⁻¹) *
          Matrix.single p q b
        = colMatrix q (fun x => elMat g x k * (a * (elMat (g⁻¹) l p * b))) := by
      calc elMat g * Matrix.single k l a * elMat (g⁻¹) * Matrix.single p q b
          = elMat g * (Matrix.single k l a *
              (elMat (g⁻¹) * Matrix.single p q b)) := by noncomm_ring
        _ = elMat g * (Matrix.single k l a *
              colMatrix q (fun x => elMat (g⁻¹) x p * b)) := by rw [mul_single_eq]
        _ = elMat g * Matrix.single k q (a * (elMat (g⁻¹) l p * b)) := by
              rw [single_mul_colMatrix]
        _ = colMatrix q (fun x => elMat g x k * (a * (elMat (g⁻¹) l p * b))) := by
              rw [mul_single_eq]
    have hA : elMat (g * elGen k l hkl a * g⁻¹)
        = 1 + elMat g * Matrix.single k l a * elMat (g⁻¹) := by
      have hs : elMat (g * elGen k l hkl a * g⁻¹)
          = elMat g * elMat (elGen k l hkl a) * elMat (g⁻¹) := rfl
      rw [hs, elMat_elGen]
      calc elMat g * (1 + Matrix.single k l a) * elMat (g⁻¹)
          = elMat g * elMat (g⁻¹) +
              elMat g * Matrix.single k l a * elMat (g⁻¹) := by noncomm_ring
        _ = 1 + elMat g * Matrix.single k l a * elMat (g⁻¹) := by
              rw [elMat_mul_inv]
    have hAi : elMat ((g * elGen k l hkl a * g⁻¹)⁻¹)
        = 1 - elMat g * Matrix.single k l a * elMat (g⁻¹) := by
      have hinv : (g * elGen k l hkl a * g⁻¹)⁻¹
          = g * (elGen k l hkl a)⁻¹ * g⁻¹ := by group
      have hs : elMat (g * (elGen k l hkl a)⁻¹ * g⁻¹)
          = elMat g * elMat ((elGen k l hkl a)⁻¹) * elMat (g⁻¹) := rfl
      rw [hinv, hs, elMat_elGen_inv]
      calc elMat g * (1 - Matrix.single k l a) * elMat (g⁻¹)
          = elMat g * elMat (g⁻¹) -
              elMat g * Matrix.single k l a * elMat (g⁻¹) := by noncomm_ring
        _ = 1 - elMat g * Matrix.single k l a * elMat (g⁻¹) := by
              rw [elMat_mul_inv]
    have hsplit : elMat (g * elGen k l hkl a * g⁻¹ * elGen p q hpq b *
          (g * elGen k l hkl a * g⁻¹)⁻¹ * (elGen p q hpq b)⁻¹)
        = elMat (g * elGen k l hkl a * g⁻¹) * elMat (elGen p q hpq b) *
          elMat ((g * elGen k l hkl a * g⁻¹)⁻¹) *
          elMat ((elGen p q hpq b)⁻¹) := rfl
    rw [hsplit, hA, hAi, elMat_elGen, elMat_elGen_inv,
      commutator_of_mul_eq_zero hXX hYY hYX, hXY]

/-- **The two proved layers, combined.**  If some `g ∈ N` admits commuting
elementary indices killing the scalar obstruction `b * g_{qk} * a` while leaving
one entry of the produced column nonzero, then `N = ⊤`. -/
theorem normal_eq_top_of_double_commutator
    (hcard : 3 ≤ Fintype.card ι)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) {k l p q : ι}
    (hkl : k ≠ l) (hpq : p ≠ q) (hlp : l ≠ p) (hqk : q ≠ k) (a b : R)
    (hobs : b * elMat g q k * a = 0)
    {x : ι} (hne : elMat g x k * (a * (elMat (g⁻¹) l p * b)) ≠ 0) :
    N = ⊤ := by
  obtain ⟨M, hM, hval⟩ :=
    exists_colMatrix_mem_of_mem N hg hkl hpq hlp hqk a b hobs
  exact normal_eq_top_of_colMatrix_mem hcard hdiv N hM hval hne

/-! ## The centre -/

theorem elMat_one : elMat (1 : elementaryGroup ι R) = 1 := rfl

/-- Off-diagonal entries of a matrix commuting with every elementary matrix
vanish. -/
theorem elMat_offDiag_eq_zero_of_commute [Nontrivial ι]
    {z : elementaryGroup ι R}
    (hz : ∀ (i j : ι), i ≠ j → ∀ a : R,
      elMat z * Matrix.single i j a = Matrix.single i j a * elMat z)
    {u i : ι} (hui : u ≠ i) : elMat z u i = 0 := by
  obtain ⟨j, hji⟩ := exists_ne i
  have h := congrFun (congrFun (hz i j (Ne.symm hji) 1) u) j
  rw [mul_single_apply, single_mul_apply, if_pos (rfl : j = j), if_neg hui,
    mul_one] at h
  exact h

/-- Diagonal entries of a matrix commuting with every elementary matrix are
central and all equal. -/
theorem elMat_diag_commute_of_commute
    {z : elementaryGroup ι R}
    (hz : ∀ (i j : ι), i ≠ j → ∀ a : R,
      elMat z * Matrix.single i j a = Matrix.single i j a * elMat z)
    {i j : ι} (hij : i ≠ j) (a : R) :
    elMat z i i * a = a * elMat z j j := by
  have h := congrFun (congrFun (hz i j hij a) i) j
  rw [mul_single_apply, single_mul_apply, if_pos (rfl : j = j),
    if_pos (rfl : i = i)] at h
  exact h

/-- **The centre of `EL_ι(R)` is trivial** as soon as the only central unit of
`R` is `1`.  For `R = L_{𝔽₂}(1,2)`, the needed coefficient-ring computation is
available separately as `BinaryLeavitt.central_units_trivial`. -/
theorem center_elementaryGroup_eq_bot [Nontrivial ι]
    (hcentral : ∀ lam : R, (∀ x : R, lam * x = x * lam) →
      (∃ mu : R, lam * mu = 1 ∧ mu * lam = 1) → lam = 1) :
    Subgroup.center (elementaryGroup ι R) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hcomm : ∀ (i j : ι), i ≠ j → ∀ a : R,
      elMat z * Matrix.single i j a = Matrix.single i j a * elMat z := by
    intro i j hij a
    have h' : elMat (elGen i j hij a * z) = elMat (z * elGen i j hij a) :=
      congrArg elMat ((Subgroup.mem_center_iff.mp hz) (elGen i j hij a))
    rw [elMat_mul, elMat_mul, elMat_elGen] at h'
    have e1 : (1 + Matrix.single i j a) * elMat z
        = elMat z + Matrix.single i j a * elMat z := by noncomm_ring
    have e2 : elMat z * (1 + Matrix.single i j a)
        = elMat z + elMat z * Matrix.single i j a := by noncomm_ring
    rw [e1, e2] at h'
    exact (add_left_cancel h').symm
  obtain ⟨i₀, i₁, hne⟩ := exists_pair_ne ι
  have hoff : ∀ u v : ι, u ≠ v → elMat z u v = 0 := fun u v huv =>
    elMat_offDiag_eq_zero_of_commute hcomm huv
  have hdiagconst : ∀ u : ι, elMat z u u = elMat z i₀ i₀ := by
    intro u
    by_cases hu : u = i₀
    · rw [hu]
    · have h := elMat_diag_commute_of_commute hcomm hu (1 : R)
      rw [mul_one, one_mul] at h
      exact h
  have hcen : ∀ x : R, elMat z i₀ i₀ * x = x * elMat z i₀ i₀ := by
    intro x
    have h := elMat_diag_commute_of_commute hcomm hne x
    rw [hdiagconst i₁] at h
    exact h
  have hmu1 : elMat z i₀ i₀ * elMat (z⁻¹) i₀ i₀ = 1 := by
    have h := congrFun (congrFun (elMat_mul_inv z) i₀) i₀
    rw [Matrix.mul_apply, Matrix.one_apply, if_pos (rfl : i₀ = i₀)] at h
    have hs : ∑ t, elMat z i₀ t * elMat (z⁻¹) t i₀
        = elMat z i₀ i₀ * elMat (z⁻¹) i₀ i₀ :=
      Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
        (fun t _ ht => by rw [hoff i₀ t (Ne.symm ht), zero_mul])
    rw [hs] at h
    exact h
  have hmu2 : elMat (z⁻¹) i₀ i₀ * elMat z i₀ i₀ = 1 := by
    have h := congrFun (congrFun (elMat_inv_mul z) i₀) i₀
    rw [Matrix.mul_apply, Matrix.one_apply, if_pos (rfl : i₀ = i₀)] at h
    have hs : ∑ t, elMat (z⁻¹) i₀ t * elMat z t i₀
        = elMat (z⁻¹) i₀ i₀ * elMat z i₀ i₀ :=
      Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
        (fun t _ ht => by rw [hoff t i₀ ht, mul_zero])
    rw [hs] at h
    exact h
  have hlam : elMat z i₀ i₀ = 1 :=
    hcentral (elMat z i₀ i₀) hcen ⟨elMat (z⁻¹) i₀ i₀, hmu1, hmu2⟩
  have hz1 : elMat z = elMat (1 : elementaryGroup ι R) := by
    rw [elMat_one]
    ext u v
    by_cases huv : u = v
    · rw [Matrix.one_apply, if_pos huv, ← huv, hdiagconst u]
      exact hlam
    · rw [Matrix.one_apply, if_neg huv]
      exact hoff u v huv
  exact Subgroup.mem_bot.mpr (elMat_injective hz1)

/-- **The centre, in the shape the coefficient-ring lemma supplies it.**  The
hypothesis is verbatim `BinaryLeavitt.central_units_trivial` for
`R = L_{𝔽₂}(1,2)`. -/
theorem center_elementaryGroup_eq_bot_of_units [Nontrivial ι]
    (hunits : ∀ u : Rˣ, (∀ y : R, (u : R) * y = y * (u : R)) → u = 1) :
    Subgroup.center (elementaryGroup ι R) = ⊥ := by
  refine center_elementaryGroup_eq_bot (fun lam hlam hinv => ?_)
  obtain ⟨mu, h1, h2⟩ := hinv
  exact congrArg Units.val (hunits ⟨lam, mu, h1, h2⟩ hlam)

/-! ## The generic statement and the reduction it feeds -/

/-- **Root detection:** every nontrivial normal subgroup of `EL_ι(R)`
contains a nonzero elementary root.  This file treats it as a generic
interface; `DiagonalNormalExtraction.rootDetection_of_leavittFamily` proves it
from the Leavitt-family inputs used by the manuscript. -/
def RootDetection (J S : Type*) [Fintype J] [DecidableEq J] [Ring S] : Prop :=
  ∀ N : Subgroup (elementaryGroup J S), N.Normal → N ≠ ⊥ →
    ∃ (i j : J) (hij : i ≠ j) (x : S), x ≠ 0 ∧ elGen i j hij x ∈ N

/-- **The exact reduction of Proposition `prop:simple`.**  Everything after
root detection is discharged by the in-repository normal-generation theorem
together with single-sandwich division. -/
theorem isSimpleGroup_of_rootDetection
    (hcard : 3 ≤ Fintype.card ι)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (hnt : Nontrivial (elementaryGroup ι R))
    (hdetect : RootDetection ι R) :
    IsSimpleGroup (elementaryGroup ι R) where
  exists_pair_ne := hnt.exists_pair_ne
  eq_bot_or_eq_top_of_normal := by
    intro N hN
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · refine Or.inr ?_
      obtain ⟨i, j, hij, x, hx, hmem⟩ := hdetect N hN hbot
      haveI : N.Normal := hN
      exact elementaryGroup_normal_eq_top_of_elGen_mem hcard N hij hmem
        (hdiv x hx)

end ElementarySimplicity
end GroupApproximation
