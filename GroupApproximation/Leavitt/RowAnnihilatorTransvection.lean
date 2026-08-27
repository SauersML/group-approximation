import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Leavitt.ElementaryTransvectionExtraction

/-!
# Row annihilators produce prescribed elementary transvections

This module proves the exchange-free half of Preusser's normal-subgroup
analysis for `EL_ι(R)`: an annihilation relation between a ring element `y` and
one entry of `σ · τ`, where `τ` is an elementary matrix with prescribed column,
forces a *prescribed* elementary transvection with a *prescribed* coefficient to
lie in any normal subgroup containing `σ`.

The statement, in the notation of Preusser's Proposition 20: if `σ ∈ N ⊴ EL_ι(R)`
and `y · (∑ p, σ_{ip} x_p) = 0` for a vector `x` with `x_j = 1`, then
`t_{kl}(a · y · x_i · b) ∈ N` for every `k ≠ l` and all `a, b ∈ R`.

## Contents

* `arrow_step_mem` is the membership form of Preusser's Lemma 19.  The published
  lemma tracks how many conjugates are needed; for membership in a normal
  subgroup that count is irrelevant, and the whole `→_{g₁,…,g_n}` bookkeeping
  collapses to a three-line identity: if `a * b ∈ N` then
  `⁅a⁻¹, g⁆ * ⁅g, b⁆ ∈ N`.
* `colUnit j x` is the elementary matrix whose `j`-th column is `x` (for `x` with
  `x j = 1`), realised as an element of `elementaryGroup ι R`.  Its membership in
  the elementary subgroup is proved by an induction over `Finset ι`, since a
  single matrix has to stand in for the product `∏_{p ≠ j} t_{pj}(x_p)`.
* `elGen_mem_of_column_annihilator` is the core two-step arrow computation.  It
  produces the transvection in one prescribed position `(j, s)`.
* `elGen_mem_of_mem_spread` moves a transvection with a fixed coefficient shape
  `a * c * b` from one position to every position, using only the Steinberg
  relation and a third index.
* `elGen_mem_of_row_annihilator` is Preusser's Proposition 20 in the form the
  exchange-consuming Proposition 21 consumes.

## The reduction word

Write `τ := colUnit j x`, `h := σ τ`, `t := t_{ri}(y)` with `r ∉ {i, j}`, and
pick `s ∉ {r, j}`.  The two elements

  `A := τ⁻¹ t⁻¹ τ`,   `B := h⁻¹ t h`

satisfy `A * B = τ⁻¹ ⁅t⁻¹, σ⁻¹⁆ τ ∈ N`, because the two `τ`-conjugations cancel
and what remains is a commutator with `σ⁻¹`.  Their defects are
`A⁻¹ = 1 + E_{ri}(y) τ` and `B = 1 + h⁻¹ E_{ri}(y) h`; the annihilation
hypothesis `y · h_{ij} = 0` says exactly that the `j`-th column of the second
defect vanishes.  One arrow step along `t_{js}(b)` therefore produces the pair

  `(t_{rs}(y x_i b), 1 + Z)`   with `Z` supported in row `j`, `Z_{jj} = 0`,

the first coordinate because `(E_{ri}(y) τ)_{rj} = y τ_{ij} = y x_i`, the second
because the vanishing column makes the commutator degenerate.  A second arrow
step along `t_{jr}(a)` turns the first coordinate into `t_{js}(a y x_i b)` and
kills the second outright, since `E_{jr}(a)` annihilates a row-`j` defect with
vanishing diagonal entry on both sides.
-/

namespace GroupApproximation

namespace RowAnnihilator

open ElementarySimplicity

open scoped BigOperators commutatorElement

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### The membership form of Preusser's Lemma 19 -/

/-- **The arrow step.**  Preusser's Lemma 19 records that `a₂ b₂` is a product of
`2ⁿ` conjugates of `a₁ b₁` and its inverse.  All that membership in a normal
subgroup needs is the one-step statement, and that is a three-line identity:
`⁅a⁻¹, g⁆ * ⁅g, b⁆ = (a⁻¹ (g (ab) g⁻¹) a) * (a⁻¹ (ab) a)⁻¹`, both factors of
which are conjugates of elements of `N`. -/
theorem arrow_step_mem {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    {a b : G} (hab : a * b ∈ N) (g : G) : ⁅a⁻¹, g⁆ * ⁅g, b⁆ ∈ N := by
  have hkey : ⁅a⁻¹, g⁆ * ⁅g, b⁆
      = a⁻¹ * (g * (a * b) * g⁻¹) * a * (a⁻¹ * (a * b) * a)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hkey]
  exact N.mul_mem (hN.conj_mem' _ (hN.conj_mem _ hab g) a)
    (N.inv_mem (hN.conj_mem' _ hab a))

/-- A commutator with a right entry in a normal subgroup lies in that subgroup. -/
theorem commutator_mem_right {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    (x : G) {n : G} (hn : n ∈ N) : ⁅x, n⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (hN.conj_mem n hn x) (N.inv_mem hn)

/-- The inverse of an elementary generator negates its coefficient. -/
theorem elGen_inv (i j : ι) (h : i ≠ j) (a : R) :
    (elGen (R := R) i j h a)⁻¹ = elGen i j h (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [elGen_mul, add_neg_cancel, elGen_zero])

/-! ### Algebraic identities for the three commutator evaluations

Each of the four unipotent products below is an instance of the square-zero
calculus of `ElementaryTransvectionExtraction`; isolating them here keeps the
main computation free of `noncomm_ring` calls. -/

/-- `(1 - S)(1 + (S + D)) = 1 + D` when `S² = 0` and `S D = 0`.  This is the
inductive step which peels one elementary factor off a column matrix. -/
theorem one_sub_single_mul_add (S D : Matrix ι ι R) (hSS : S * S = 0)
    (hSD : S * D = 0) : (1 - S) * (1 + (S + D)) = 1 + D := by
  have e : (1 - S) * (1 + (S + D)) = 1 + D - S * S - S * D := by noncomm_ring
  rw [e, hSS, hSD, sub_zero, sub_zero]

/-- Conjugating a unipotent by the column matrix `1 + D`: when `D² = 0` and
`D S = 0` the conjugate is again unipotent, with defect `S (1 + D)`. -/
theorem colConj_val_eq (D S : Matrix ι ι R) (hDD : D * D = 0) (hDS : D * S = 0) :
    (1 - D) * (1 + S) * (1 + D) = 1 + S * (1 + D) := by
  have e : (1 - D) * (1 + S) * (1 + D)
      = 1 + S * (1 + D) - D * D - D * S - D * S * D := by noncomm_ring
  rw [e, hDD, hDS, zero_mul, sub_zero, sub_zero, sub_zero]

/-- Conjugating a unipotent by an arbitrary invertible matrix. -/
theorem conj_val_eq (Hi H S : Matrix ι ι R) (hHiH : Hi * H = 1) :
    Hi * (1 + S) * H = 1 + Hi * S * H := by
  have e : Hi * (1 + S) * H = Hi * H + Hi * S * H := by noncomm_ring
  rw [e, hHiH]

/-- The conjugate of a square-zero matrix is square-zero. -/
theorem conj_single_mul_self (Hi H S : Matrix ι ι R) (hHHi : H * Hi = 1)
    (hSS : S * S = 0) : Hi * S * H * (Hi * S * H) = 0 := by
  have e : Hi * S * H * (Hi * S * H) = Hi * S * (H * Hi) * S * H := by noncomm_ring
  rw [e, hHHi, mul_one, mul_assoc Hi S S, hSS, mul_zero, zero_mul]

/-- The defect `E_{ri}(y) T` of a `T`-conjugated root squares to zero as soon as
`T_{ir} = 0`. -/
theorem row_conj_mul_self (T : Matrix ι ι R) (r i : ι) (y : R) (hTir : T i r = 0) :
    Matrix.single r i y * T * (Matrix.single r i y * T) = 0 := by
  rw [← mul_assoc, Matrix.single_mul_mul_single, hTir, mul_zero, zero_mul,
    Matrix.single_zero, zero_mul]

/-- **The sandwich entry formula.**  `(M E_{ri}(y) M')_{pq} = M_{pr} y M'_{iq}`. -/
theorem triple_single_apply (M M' : Matrix ι ι R) (r i : ι) (y : R) (p q : ι) :
    (M * Matrix.single r i y * M') p q = M p r * y * M' i q := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [matrix_mul_single_apply, if_pos rfl]
  · intro m _ hm
    rw [matrix_mul_single_apply, if_neg hm, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-! ### The elementary matrix with a prescribed column

Preusser's argument replaces `σ` by `σ τ` where `τ = ∏_{p ≠ j} t_{pj}(x_p)`.
The product has to be available as a *single* matrix (for entry computations)
which is simultaneously an element of `EL_ι(R)` (so that conjugation by it
preserves a normal subgroup).  Both are supplied below. -/

omit [Fintype ι] in
/-- Entry formula for a partial column sum of single-entry matrices. -/
theorem sum_single_apply (j : ι) (x : ι → R) (s : Finset ι) (p q : ι) :
    (∑ m ∈ s, Matrix.single m j (x m)) p q =
      if q = j then (if p ∈ s then x p else 0) else 0 := by
  classical
  rw [Matrix.sum_apply]
  by_cases hq : q = j
  · rw [if_pos hq]
    by_cases hp : p ∈ s
    · rw [if_pos hp, Finset.sum_eq_single p]
      · rw [Matrix.single_apply, if_pos ⟨rfl, hq.symm⟩]
      · intro m _ hmp
        rw [Matrix.single_apply, if_neg (fun h => hmp h.1)]
      · intro hcon
        exact absurd hp hcon
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Matrix.single_apply]
      refine if_neg ?_
      rintro ⟨rfl, -⟩
      exact hp hm
  · rw [if_neg hq]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.single_apply]
    refine if_neg ?_
    rintro ⟨-, hjq⟩
    exact hq hjq.symm

/-- The off-diagonal defect of the elementary matrix whose `j`-th column is `x`. -/
def colDefect (j : ι) (x : ι → R) : Matrix ι ι R :=
  ∑ m ∈ Finset.univ.erase j, Matrix.single m j (x m)

theorem colDefect_def (j : ι) (x : ι → R) :
    colDefect j x = ∑ m ∈ Finset.univ.erase j, Matrix.single m j (x m) := rfl

theorem colDefect_apply (j : ι) (x : ι → R) (p q : ι) :
    colDefect j x p q = if q = j then (if p = j then 0 else x p) else 0 := by
  classical
  rw [colDefect_def, sum_single_apply]
  by_cases hp : p = j
  · rw [if_neg (fun hmem => (Finset.mem_erase.mp hmem).1 hp), if_pos hp]
  · rw [if_pos (Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩), if_neg hp]

theorem colDefect_apply_of_ne (j : ι) (x : ι → R) (p : ι) {q : ι} (hq : q ≠ j) :
    colDefect j x p q = 0 := by
  rw [colDefect_apply, if_neg hq]

theorem colDefect_apply_row (j : ι) (x : ι → R) (q : ι) : colDefect j x j q = 0 := by
  rw [colDefect_apply]
  by_cases hq : q = j
  · rw [if_pos hq, if_pos rfl]
  · rw [if_neg hq]

theorem colDefect_mul_self (j : ι) (x : ι → R) :
    colDefect j x * colDefect j x = 0 := by
  classical
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m = j
  · rw [hm, colDefect_apply_row, mul_zero]
  · rw [colDefect_apply_of_ne j x p hm, zero_mul]

/-- The unipotent matrix whose `j`-th column is `x` (up to the diagonal). -/
def colUnitMat (j : ι) (x : ι → R) : (Matrix ι ι R)ˣ :=
  sqZeroUnit (colDefect j x) (colDefect_mul_self j x)

theorem colUnitMat_val (j : ι) (x : ι → R) :
    (colUnitMat j x : Matrix ι ι R) = 1 + colDefect j x := rfl

/-- **A column matrix is elementary.**  The induction peels off one factor
`t_{pj}(x_p)` at a time; the peeled factor annihilates the remaining sum because
row `j` of that sum vanishes. -/
theorem mem_elementaryGroup_of_sum_single (j : ι) (x : ι → R) :
    ∀ s : Finset ι, j ∉ s → ∀ u : (Matrix ι ι R)ˣ,
      (u : Matrix ι ι R) = 1 + ∑ m ∈ s, Matrix.single m j (x m) →
      u ∈ elementaryGroup ι R := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ u hu
      rw [Finset.sum_empty, add_zero] at hu
      have hu1 : u = 1 := by
        apply Units.ext
        exact hu
      rw [hu1]
      exact Subgroup.one_mem _
  | insert p s hps ih =>
      intro hj u hu
      have hjp : j ≠ p := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
      have hjs : j ∉ s := fun h => hj (Finset.mem_insert.mpr (Or.inr h))
      have hpj : p ≠ j := fun h => hjp h.symm
      have hDj : ∀ d : ι, (∑ m ∈ s, Matrix.single m j (x m)) j d = 0 := by
        intro d
        rw [sum_single_apply]
        by_cases hd : d = j
        · rw [if_pos hd, if_neg hjs]
        · rw [if_neg hd]
      have hzero :
          Matrix.single p j (x p) * (∑ m ∈ s, Matrix.single m j (x m)) = 0 := by
        ext c d
        rw [matrix_single_mul_apply, Matrix.zero_apply]
        by_cases hc : c = p
        · rw [if_pos hc, hDj d, mul_zero]
        · rw [if_neg hc]
      have hv : (((elementaryUnit p j hpj (x p))⁻¹ * u : (Matrix ι ι R)ˣ) :
            Matrix ι ι R) = 1 + ∑ m ∈ s, Matrix.single m j (x m) := by
        rw [Units.val_mul, hu, Finset.sum_insert hps]
        exact one_sub_single_mul_add (Matrix.single p j (x p))
          (∑ m ∈ s, Matrix.single m j (x m))
          (single_mul_self_eq_zero p j hpj (x p)) hzero
      have hvmem := ih hjs _ hv
      have hu' : u = elementaryUnit p j hpj (x p) *
          ((elementaryUnit p j hpj (x p))⁻¹ * u) := by group
      rw [hu']
      exact Subgroup.mul_mem _ (elementaryUnit_mem p j hpj (x p)) hvmem

theorem colUnitMat_mem (j : ι) (x : ι → R) :
    colUnitMat j x ∈ elementaryGroup ι R :=
  mem_elementaryGroup_of_sum_single j x (Finset.univ.erase j)
    (Finset.notMem_erase j Finset.univ) _ rfl

/-- The element of `EL_ι(R)` whose matrix has `j`-th column `x`. -/
def colUnit (j : ι) (x : ι → R) : elementaryGroup ι R :=
  ⟨colUnitMat j x, colUnitMat_mem j x⟩

theorem elMat_colUnit (j : ι) (x : ι → R) :
    elMat (colUnit j x) = 1 + colDefect j x := rfl

theorem elMat_colUnit_inv (j : ι) (x : ι → R) :
    elMat ((colUnit j x)⁻¹) = 1 - colDefect j x := rfl

/-- The prescribed column, in the presence of the normalisation `x j = 1`. -/
theorem elMat_colUnit_apply_col {j : ι} {x : ι → R} (hxj : x j = 1) (p : ι) :
    elMat (colUnit j x) p j = x p := by
  rw [elMat_colUnit, Matrix.add_apply, colDefect_apply, if_pos rfl]
  by_cases hp : p = j
  · rw [if_pos hp, hp, Matrix.one_apply_eq, add_zero, hxj]
  · rw [if_neg hp, Matrix.one_apply_ne hp, zero_add]

/-- Away from column `j` the column matrix is the identity. -/
theorem elMat_colUnit_apply_of_ne (j : ι) (x : ι → R) (p : ι) {q : ι} (hq : q ≠ j) :
    elMat (colUnit j x) p q = if p = q then 1 else 0 := by
  rw [elMat_colUnit, Matrix.add_apply, colDefect_apply_of_ne j x p hq, add_zero,
    Matrix.one_apply]

/-! ### The core two-step arrow computation

This is Preusser's Proposition 20 with the position of the resulting
transvection still pinned to the pair `(j, s)` supplied by the reduction word.
Spreading it over all positions is the separate, purely Steinberg-theoretic step
`elGen_mem_of_mem_spread` below. -/

/-- **Preusser's Proposition 20, in one prescribed position.**  If `g` lies in a
normal subgroup of `EL_ι(R)` and `y` annihilates the `(i, j)` entry of
`g · colUnit j x` on the left, then `t_{js}(a y x_i b)` lies in that normal
subgroup, for every `a, b` and every admissible pair of auxiliary indices.

The hypothesis is exactly Preusser's `y ∑_p σ_{ip} x_p = 0`: the entry
`(g · colUnit j x)_{ij}` *is* `∑_p g_{ip} x_p` once `x j = 1`, which is what
`elGen_mem_of_row_annihilator` records. -/
theorem elGen_mem_of_column_annihilator
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N)
    {j : ι} {x : ι → R} (hxj : x j = 1) {i : ι} {y : R}
    (hann : y * elMat (g * colUnit j x) i j = 0)
    {r s : ι} (hri : r ≠ i) (hrj : r ≠ j) (hjs : j ≠ s) (hrs : r ≠ s)
    (a b : R) :
    elGen j s hjs (a * y * x i * b) ∈ N := by
  classical
  have hir : i ≠ r := Ne.symm hri
  have hjr : j ≠ r := Ne.symm hrj
  have hsj : s ≠ j := Ne.symm hjs
  have hsr : s ≠ r := Ne.symm hrs
  -- entries of the column matrix
  have hTir : elMat (colUnit j x) i r = 0 := by
    rw [elMat_colUnit_apply_of_ne j x i hrj, if_neg hir]
  have hTij : elMat (colUnit j x) i j = x i := elMat_colUnit_apply_col hxj i
  have hSS : Matrix.single r i y * Matrix.single r i y = 0 :=
    single_mul_self_eq_zero r i hri y
  have hDS : colDefect j x * Matrix.single r i y = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = i
    · rw [if_pos hq, colDefect_apply_of_ne j x p hrj, zero_mul]
    · rw [if_neg hq]
  -- the defect of the root conjugated by the column matrix
  have hYY : Matrix.single r i y * elMat (colUnit j x) *
      (Matrix.single r i y * elMat (colUnit j x)) = 0 :=
    row_conj_mul_self (elMat (colUnit j x)) r i y hTir
  have hA1 : (((colUnit j x)⁻¹ * elGen r i hri y * colUnit j x :
        elementaryGroup ι R) : (Matrix ι ι R)ˣ)
      = sqZeroUnit (Matrix.single r i y * elMat (colUnit j x)) hYY := by
    apply Units.ext
    show elMat ((colUnit j x)⁻¹ * elGen r i hri y * colUnit j x)
        = 1 + Matrix.single r i y * elMat (colUnit j x)
    rw [elMat_mul ((colUnit j x)⁻¹ * elGen r i hri y) (colUnit j x),
      elMat_mul ((colUnit j x)⁻¹) (elGen r i hri y), elMat_colUnit_inv,
      elMat_elGen, elMat_colUnit]
    exact colConj_val_eq (colDefect j x) (Matrix.single r i y)
      (colDefect_mul_self j x) hDS
  -- the defect of the root conjugated by `g · colUnit j x`
  have hWW : elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
      elMat (g * colUnit j x) *
      (elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
        elMat (g * colUnit j x)) = 0 :=
    conj_single_mul_self (elMat ((g * colUnit j x)⁻¹)) (elMat (g * colUnit j x))
      (Matrix.single r i y) (elMat_mul_inv (g * colUnit j x)) hSS
  have hB1 : ((((g * colUnit j x)⁻¹ * elGen r i hri y * (g * colUnit j x)) :
        elementaryGroup ι R) : (Matrix ι ι R)ˣ)
      = sqZeroUnit (elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
          elMat (g * colUnit j x)) hWW := by
    apply Units.ext
    show elMat ((g * colUnit j x)⁻¹ * elGen r i hri y * (g * colUnit j x))
        = 1 + elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
            elMat (g * colUnit j x)
    rw [elMat_mul ((g * colUnit j x)⁻¹ * elGen r i hri y) (g * colUnit j x),
      elMat_mul ((g * colUnit j x)⁻¹) (elGen r i hri y), elMat_elGen]
    exact conj_val_eq (elMat ((g * colUnit j x)⁻¹)) (elMat (g * colUnit j x))
      (Matrix.single r i y) (elMat_inv_mul (g * colUnit j x))
  -- the annihilation hypothesis kills the whole `j`-th column of that defect
  have hWcol : ∀ p : ι, (elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
      elMat (g * colUnit j x)) p j = 0 := by
    intro p
    rw [triple_single_apply, mul_assoc, hann, mul_zero]
  -- the start of the arrow chain
  have h0 : ((colUnit j x)⁻¹ * (elGen r i hri y)⁻¹ * colUnit j x) *
      ((g * colUnit j x)⁻¹ * elGen r i hri y * (g * colUnit j x)) ∈ N := by
    have hcm : (elGen r i hri y)⁻¹ * g⁻¹ * elGen r i hri y * g ∈ N := by
      refine N.mul_mem ?_ hg
      have hcj := hN.conj_mem g⁻¹ (N.inv_mem hg) (elGen r i hri y)⁻¹
      rwa [inv_inv] at hcj
    have hkey : ((colUnit j x)⁻¹ * (elGen r i hri y)⁻¹ * colUnit j x) *
        ((g * colUnit j x)⁻¹ * elGen r i hri y * (g * colUnit j x))
        = (colUnit j x)⁻¹ *
            ((elGen r i hri y)⁻¹ * g⁻¹ * elGen r i hri y * g) * colUnit j x := by
      group
    rw [hkey]
    exact hN.conj_mem' _ hcm (colUnit j x)
  have h1 := arrow_step_mem N h0 (elGen j s hjs b)
  have hA1inv : ((colUnit j x)⁻¹ * (elGen r i hri y)⁻¹ * colUnit j x :
        elementaryGroup ι R)⁻¹
      = (colUnit j x)⁻¹ * elGen r i hri y * colUnit j x := by group
  rw [hA1inv] at h1
  -- first arrow step, first coordinate: the coefficient `y x_i b` appears
  have hFY : Matrix.single j s b *
      (Matrix.single r i y * elMat (colUnit j x)) = 0 := by
    rw [← mul_assoc, Matrix.single_mul_single_of_ne (c := b) j s r hsr y, zero_mul]
  have hc1 : ⁅((colUnit j x)⁻¹ * elGen r i hri y * colUnit j x :
        elementaryGroup ι R), elGen j s hjs b⁆
      = elGen r s hrs (y * x i * b) := by
    apply Subtype.ext
    show ⁅(((colUnit j x)⁻¹ * elGen r i hri y * colUnit j x :
        elementaryGroup ι R) : (Matrix ι ι R)ˣ), elementaryUnit j s hjs b⁆
      = elementaryUnit r s hrs (y * x i * b)
    rw [hA1]
    apply Units.ext
    show (1 + Matrix.single r i y * elMat (colUnit j x)) *
        (1 + Matrix.single j s b) *
        (1 - Matrix.single r i y * elMat (colUnit j x)) *
        (1 - Matrix.single j s b)
      = 1 + Matrix.single r s (y * x i * b)
    rw [unipotent_commutator_of_right_annihilates _ _ hYY
        (single_mul_self_eq_zero j s hjs b) hFY,
      Matrix.single_mul_mul_single, hTij]
  rw [hc1] at h1
  -- first arrow step, second coordinate: a one-row defect with zero diagonal
  have hZrow : IsRowSupported (Matrix.single j s b *
      (elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
        elMat (g * colUnit j x))) j := by
    intro p q hp
    rw [matrix_single_mul_apply, if_neg hp]
  have hZjj : (Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
      Matrix.single r i y * elMat (g * colUnit j x))) j j = 0 := by
    rw [matrix_single_mul_apply, if_pos rfl, hWcol s, mul_zero]
  have hZZ : Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
        Matrix.single r i y * elMat (g * colUnit j x)) *
      (Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
        Matrix.single r i y * elMat (g * colUnit j x))) = 0 :=
    IsRowSupported.mul_self hZrow hZjj
  have hWF : elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
      elMat (g * colUnit j x) * Matrix.single j s b = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = s
    · rw [if_pos hq, hWcol p, zero_mul]
    · rw [if_neg hq]
  have hc2 : ((⁅elGen j s hjs b,
        ((g * colUnit j x)⁻¹ * elGen r i hri y * (g * colUnit j x) :
          elementaryGroup ι R)⁆ : elementaryGroup ι R) : (Matrix ι ι R)ˣ)
      = sqZeroUnit (Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
          Matrix.single r i y * elMat (g * colUnit j x))) hZZ := by
    show ⁅elementaryUnit j s hjs b,
        ((((g * colUnit j x)⁻¹ * elGen r i hri y * (g * colUnit j x)) :
          elementaryGroup ι R) : (Matrix ι ι R)ˣ)⁆ = _
    rw [hB1]
    apply Units.ext
    show (1 + Matrix.single j s b) *
        (1 + elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
          elMat (g * colUnit j x)) *
        (1 - Matrix.single j s b) *
        (1 - elMat ((g * colUnit j x)⁻¹) * Matrix.single r i y *
          elMat (g * colUnit j x))
      = 1 + Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
          Matrix.single r i y * elMat (g * colUnit j x))
    exact unipotent_commutator_of_right_annihilates _ _
      (single_mul_self_eq_zero j s hjs b) hWW hWF
  -- second arrow step: the junk coordinate dies, the good one gains `a`
  have h2 := arrow_step_mem N h1 (elGen j r hjr a)
  have hGZ : Matrix.single j r a *
      (Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
        Matrix.single r i y * elMat (g * colUnit j x))) = 0 := by
    ext p q
    rw [matrix_single_mul_apply, Matrix.zero_apply]
    by_cases hp : p = j
    · rw [if_pos hp, hZrow r q hrj, mul_zero]
    · rw [if_neg hp]
  have hZG : Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
        Matrix.single r i y * elMat (g * colUnit j x)) *
      Matrix.single j r a = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = r
    · rw [if_pos hq]
      by_cases hp : p = j
      · rw [hp, hZjj, zero_mul]
      · rw [hZrow p j hp, zero_mul]
    · rw [if_neg hq]
  have hc3 : (⁅elGen j r hjr a,
      ⁅elGen j s hjs b, ((g * colUnit j x)⁻¹ * elGen r i hri y *
        (g * colUnit j x) : elementaryGroup ι R)⁆⁆ : elementaryGroup ι R) = 1 := by
    apply Subtype.ext
    show ⁅elementaryUnit j r hjr a,
        ((⁅elGen j s hjs b, ((g * colUnit j x)⁻¹ * elGen r i hri y *
          (g * colUnit j x) : elementaryGroup ι R)⁆ : elementaryGroup ι R) :
            (Matrix ι ι R)ˣ)⁆ = 1
    rw [hc2]
    apply Units.ext
    show (1 + Matrix.single j r a) *
        (1 + Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
          Matrix.single r i y * elMat (g * colUnit j x))) *
        (1 - Matrix.single j r a) *
        (1 - Matrix.single j s b * (elMat ((g * colUnit j x)⁻¹) *
          Matrix.single r i y * elMat (g * colUnit j x))) = 1
    rw [unipotent_commutator _ _ (single_mul_self_eq_zero j r hjr a) hZZ, hGZ, hZG]
    simp
  have hc4 : ⁅((elGen r s hrs (y * x i * b))⁻¹ : elementaryGroup ι R),
        elGen j r hjr a⁆ = elGen j s hjs (a * (y * x i * b)) := by
    rw [elGen_inv]
    apply Subtype.ext
    show ⁅elementaryUnit r s hrs (-(y * x i * b)), elementaryUnit j r hjr a⁆
      = elementaryUnit j s hjs (a * (y * x i * b))
    apply Units.ext
    show (1 + Matrix.single r s (-(y * x i * b))) * (1 + Matrix.single j r a) *
        (1 - Matrix.single r s (-(y * x i * b))) * (1 - Matrix.single j r a)
      = 1 + Matrix.single j s (a * (y * x i * b))
    rw [unipotent_commutator_of_left_annihilates _ _
        (single_mul_self_eq_zero r s hrs (-(y * x i * b)))
        (single_mul_self_eq_zero j r hjr a)
        (Matrix.single_mul_single_of_ne (c := -(y * x i * b)) r s j hsj a),
      Matrix.single_mul_single_same, mul_neg, ← Matrix.single_neg, sub_neg_eq_add]
  rw [hc4, hc3, mul_one] at h2
  have hcoef : a * (y * x i * b) = a * y * x i * b := by
    rw [← mul_assoc, ← mul_assoc]
  rwa [hcoef] at h2

/-! ### Spreading one transvection over all positions -/

/-- **From one position to all positions.**  A normal subgroup containing
`t_{pq}(a c b)` for a fixed pair `p ≠ q` and *all* `a, b` contains
`t_{kl}(a c b)` for every pair `k ≠ l`.  Only the Steinberg relation and a third
index are used. -/
theorem elGen_mem_of_mem_spread (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] {c : R}
    {p q : ι} (hpq : p ≠ q)
    (hbase : ∀ a b : R, elGen p q hpq (a * c * b) ∈ N)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elGen k l hkl (a * c * b) ∈ N := by
  classical
  -- row `p`, arbitrary column
  have hrow : ∀ (m : ι) (hpm : p ≠ m) (a b : R), elGen p m hpm (a * c * b) ∈ N := by
    intro m hpm a b
    by_cases hmq : m = q
    · subst hmq
      exact hbase a b
    · have hqm : q ≠ m := fun h => hmq h.symm
      have hmem : ⁅elGen p q hpq (a * c * b), elGen q m hqm 1⁆ ∈ N :=
        commutator_mem_left N (hbase a b) _
      rw [commutatorElement_def,
        elGen_commutator p q m hpq hqm hpm (a * c * b) 1, mul_one] at hmem
      exact hmem
  -- every position whose two indices avoid `p`
  have hgen : ∀ (u v : ι) (huv : u ≠ v), u ≠ p → p ≠ v → ∀ a b : R,
      elGen u v huv (a * c * b) ∈ N := by
    intro u v huv hup hpv a b
    have hmem : ⁅elGen u p hup a, elGen p v hpv (1 * c * b)⁆ ∈ N :=
      commutator_mem_right N _ (hrow v hpv 1 b)
    rw [commutatorElement_def,
      elGen_commutator u p v hup hpv huv a (1 * c * b), one_mul,
      ← mul_assoc] at hmem
    exact hmem
  by_cases hkp : k = p
  · subst hkp
    exact hrow l hkl a b
  · by_cases hpl : p = l
    · -- the target column is `p`; route through a third index
      obtain ⟨m, hmk, hmp⟩ := exists_third_index hcard k p
      have hkm : k ≠ m := fun h => hmk h.symm
      have hpm : p ≠ m := fun h => hmp h.symm
      have hml : m ≠ l := fun h => hmp (h.trans hpl.symm)
      have hmem : ⁅elGen k m hkm (a * c * b), elGen m l hml 1⁆ ∈ N :=
        commutator_mem_left N (hgen k m hkm hkp hpm a b) _
      rw [commutatorElement_def,
        elGen_commutator k m l hkm hml hkl (a * c * b) 1, mul_one] at hmem
      exact hmem
    · exact hgen k l hkl hkp hpl a b

/-! ### Preusser's Proposition 20 -/

/-- **Preusser, Proposition 20** (arXiv:1912.11386), in membership form.

Let `N` be a normal subgroup of `EL_ι(R)` with `3 ≤ card ι`, let `g ∈ N`, and
let `x : ι → R` be a vector with `x j = 1` for some index `j`.  If `y`
annihilates the `i`-th coordinate of `g · x` on the left, then the elementary
transvection `t_{kl}(a y x_i b)` lies in `N`, for every `k ≠ l` and all
`a, b ∈ R`.

Preusser's statement also counts the conjugates needed (eight); the count is
irrelevant to membership and is not tracked here. -/
theorem elGen_mem_of_row_annihilator (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N)
    (i j : ι) (x : ι → R) (y : R) (hxj : x j = 1)
    (hann : y * (∑ p, elMat g i p * x p) = 0)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elGen k l hkl (a * y * x i * b) ∈ N := by
  classical
  obtain ⟨r, hri, hrj⟩ := exists_third_index hcard i j
  obtain ⟨s, hsr, hsj⟩ := exists_third_index hcard r j
  have hjs : j ≠ s := Ne.symm hsj
  have hrs : r ≠ s := Ne.symm hsr
  have hann' : y * elMat (g * colUnit j x) i j = 0 := by
    have he : elMat (g * colUnit j x) i j = ∑ p, elMat g i p * x p := by
      rw [elMat_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [elMat_colUnit_apply_col hxj p]
    rw [he]
    exact hann
  have hbase : ∀ a b : R, elGen j s hjs (a * (y * x i) * b) ∈ N := by
    intro a b
    have h := elGen_mem_of_column_annihilator N hg hxj hann' hri hrj hjs hrs a b
    rwa [mul_assoc a y (x i)] at h
  rw [mul_assoc a y (x i)]
  exact elGen_mem_of_mem_spread hcard N hjs hbase hkl a b

end RowAnnihilator

end GroupApproximation
