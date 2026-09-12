import GroupApproximation.Leavitt.PreusserNormalizedByCore

/-!
# Preusser's Proposition 20 for a subgroup normalized by `EL_ι(R)`

`RowAnnihilator.elGen_mem_of_row_annihilator` proves Preusser's Proposition 20
for a **normal subgroup of `EL_ι(R)`**: if `σ ∈ N ⊴ EL_ι(R)` and
`y · (∑_p σ_{ip} x_p) = 0` for a vector `x` with `x_j = 1`, then
`t_{kl}(a · y · x_i · b) ∈ N` for every `k ≠ l` and all `a, b ∈ R`.

Preusser states it for `σ ∈ GL_ι(R)`, with the conclusion landing in any
subgroup `H ≤ GL_ι(R)` that contains `σ` and is **normalized by** `EL_ι(R)`.
This file proves that form, by rerunning the same reduction word one level up.

## Why the same word works

Every element that the reduction word *conjugates by* is elementary:

* the column matrix `τ = colUnitMat j x` and the root `t = t_{ri}(y)`, in the
  start of the chain `A · B = τ⁻¹ ⁅t⁻¹, σ⁻¹⁆ τ`;
* the roots `t_{js}(b)` and `t_{jr}(a)` in the two arrow steps.

The general linear element `σ` appears only inside `B = (στ)⁻¹ t (στ)`, which
is never conjugated -- it is the passive argument `b` of the arrow step.  So
`NormalizedBy.arrow_step_mem` (`Leavitt.PreusserNormalizedByCore`), whose two
conjugating arguments are required to lie in `EL_ι(R)` and whose passive
argument is unrestricted, replaces `RowAnnihilator.arrow_step_mem` verbatim,
and normality of `H` inside `EL_ι(R)` is never used.

All matrix identities -- the square-zero calculus, the entry formulas for the
column matrix, the three commutator evaluations -- are reused unchanged from
`Leavitt.RowAnnihilatorTransvection`; only the group in which the word is read
has changed, from `elementaryGroup ι R` to `(Matrix ι ι R)ˣ`.

## Contents

* `elementaryUnit_mem_of_column_annihilator` — the core two-step arrow
  computation, producing the transvection in the one position `(j, s)`.
* `elementaryUnit_mem_of_mem_spread` — spreading a transvection with the
  coefficient shape `a * c * b` from one position to every position.
* `elementaryUnit_mem_of_row_annihilator` — Preusser's Proposition 20 in the
  form Proposition 21 consumes.
-/

namespace GroupApproximation
namespace PreusserNormalizedBy

open ElementarySimplicity RowAnnihilator

open scoped BigOperators commutatorElement

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### The core two-step arrow computation -/

/-- **Preusser's Proposition 20, in one prescribed position, for a subgroup
normalized by `EL_ι(R)`.**

If `g` lies in a subgroup `H ≤ GL_ι(R)` normalized by `EL_ι(R)` and `y`
annihilates the `(i, j)` entry of `g · colUnitMat j x` on the left, then
`t_{js}(a y x_i b) ∈ H`, for every `a, b` and every admissible pair of
auxiliary indices. -/
theorem elementaryUnit_mem_of_column_annihilator
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {g : (Matrix ι ι R)ˣ} (hg : g ∈ H)
    {j : ι} {x : ι → R} (hxj : x j = 1) {i : ι} {y : R}
    (hann : y * glMat (g * colUnitMat j x) i j = 0)
    {r s : ι} (hri : r ≠ i) (hrj : r ≠ j) (hjs : j ≠ s) (hrs : r ≠ s)
    (a b : R) :
    elementaryUnit j s hjs (a * y * x i * b) ∈ H := by
  classical
  have hir : i ≠ r := Ne.symm hri
  have hjr : j ≠ r := Ne.symm hrj
  have hsj : s ≠ j := Ne.symm hjs
  have hsr : s ≠ r := Ne.symm hrs
  -- entries of the column matrix
  have hTir : glMat (colUnitMat j x) i r = 0 := by
    rw [glMat_colUnitMat_apply_of_ne j x i hrj, if_neg hir]
  have hTij : glMat (colUnitMat j x) i j = x i :=
    glMat_colUnitMat_apply_col hxj i
  have hSS : Matrix.single r i y * Matrix.single r i y = 0 :=
    single_mul_self_eq_zero r i hri y
  have hDS : colDefect j x * Matrix.single r i y = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = i
    · rw [if_pos hq, colDefect_apply_of_ne j x p hrj, zero_mul]
    · rw [if_neg hq]
  -- the defect of the root conjugated by the column matrix
  have hYY : Matrix.single r i y * glMat (colUnitMat j x) *
      (Matrix.single r i y * glMat (colUnitMat j x)) = 0 :=
    row_conj_mul_self (glMat (colUnitMat j x)) r i y hTir
  have hA1 : ((colUnitMat j x)⁻¹ * elementaryUnit r i hri y *
        colUnitMat j x : (Matrix ι ι R)ˣ)
      = sqZeroUnit (Matrix.single r i y * glMat (colUnitMat j x)) hYY := by
    apply Units.ext
    show glMat ((colUnitMat j x)⁻¹ * elementaryUnit r i hri y * colUnitMat j x)
        = 1 + Matrix.single r i y * glMat (colUnitMat j x)
    rw [glMat_mul, glMat_mul, glMat_colUnitMat_inv, glMat_elementaryUnit,
      glMat_colUnitMat]
    exact colConj_val_eq (colDefect j x) (Matrix.single r i y)
      (colDefect_mul_self j x) hDS
  -- the defect of the root conjugated by `g · colUnitMat j x`
  have hWW : glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
      glMat (g * colUnitMat j x) *
      (glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
        glMat (g * colUnitMat j x)) = 0 :=
    conj_single_mul_self (glMat ((g * colUnitMat j x)⁻¹))
      (glMat (g * colUnitMat j x)) (Matrix.single r i y)
      (glMat_mul_inv (g * colUnitMat j x)) hSS
  have hB1 : ((g * colUnitMat j x)⁻¹ * elementaryUnit r i hri y *
        (g * colUnitMat j x) : (Matrix ι ι R)ˣ)
      = sqZeroUnit (glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
          glMat (g * colUnitMat j x)) hWW := by
    apply Units.ext
    show glMat ((g * colUnitMat j x)⁻¹ * elementaryUnit r i hri y *
          (g * colUnitMat j x))
        = 1 + glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
            glMat (g * colUnitMat j x)
    rw [glMat_mul, glMat_mul, glMat_elementaryUnit]
    exact conj_val_eq (glMat ((g * colUnitMat j x)⁻¹))
      (glMat (g * colUnitMat j x)) (Matrix.single r i y)
      (glMat_inv_mul (g * colUnitMat j x))
  -- the annihilation hypothesis kills the whole `j`-th column of that defect
  have hWcol : ∀ p : ι, (glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
      glMat (g * colUnitMat j x)) p j = 0 := by
    intro p
    rw [triple_single_apply, mul_assoc, hann, mul_zero]
  -- the two elementary memberships the arrow steps need
  have hTmem : colUnitMat j x ∈ elementaryGroup ι R :=
    colUnitMat_mem_elementaryGroup j x
  have hAmem : ((colUnitMat j x)⁻¹ * (elementaryUnit r i hri y)⁻¹ *
      colUnitMat j x : (Matrix ι ι R)ˣ) ∈ elementaryGroup ι R :=
    Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hTmem)
        (Subgroup.inv_mem _ (elementaryUnit_mem r i hri y))) hTmem
  -- the start of the arrow chain
  have h0 : ((colUnitMat j x)⁻¹ * (elementaryUnit r i hri y)⁻¹ *
      colUnitMat j x) *
      ((g * colUnitMat j x)⁻¹ * elementaryUnit r i hri y *
        (g * colUnitMat j x)) ∈ H := by
    have hcm : (elementaryUnit r i hri y)⁻¹ * g⁻¹ * elementaryUnit r i hri y *
        g ∈ H :=
      H.mul_mem (hnorm.conj_mem' (elementaryUnit_mem r i hri y) (H.inv_mem hg))
        hg
    have hkey : ((colUnitMat j x)⁻¹ * (elementaryUnit r i hri y)⁻¹ *
          colUnitMat j x) *
        ((g * colUnitMat j x)⁻¹ * elementaryUnit r i hri y *
          (g * colUnitMat j x))
        = (colUnitMat j x)⁻¹ *
            ((elementaryUnit r i hri y)⁻¹ * g⁻¹ * elementaryUnit r i hri y * g) *
            colUnitMat j x := by
      group
    rw [hkey]
    exact hnorm.conj_mem' hTmem hcm
  have h1 := hnorm.arrow_step_mem h0 hAmem (elementaryUnit_mem j s hjs b)
  have hA1inv : ((colUnitMat j x)⁻¹ * (elementaryUnit r i hri y)⁻¹ *
        colUnitMat j x : (Matrix ι ι R)ˣ)⁻¹
      = (colUnitMat j x)⁻¹ * elementaryUnit r i hri y * colUnitMat j x := by
    group
  rw [hA1inv] at h1
  -- first arrow step, first coordinate: the coefficient `y x_i b` appears
  have hFY : Matrix.single j s b *
      (Matrix.single r i y * glMat (colUnitMat j x)) = 0 := by
    rw [← mul_assoc, Matrix.single_mul_single_of_ne (c := b) j s r hsr y,
      zero_mul]
  have hc1 : ⁅((colUnitMat j x)⁻¹ * elementaryUnit r i hri y *
        colUnitMat j x : (Matrix ι ι R)ˣ), elementaryUnit j s hjs b⁆
      = elementaryUnit r s hrs (y * x i * b) := by
    rw [hA1]
    apply Units.ext
    show (1 + Matrix.single r i y * glMat (colUnitMat j x)) *
        (1 + Matrix.single j s b) *
        (1 - Matrix.single r i y * glMat (colUnitMat j x)) *
        (1 - Matrix.single j s b)
      = 1 + Matrix.single r s (y * x i * b)
    rw [unipotent_commutator_of_right_annihilates _ _ hYY
        (single_mul_self_eq_zero j s hjs b) hFY,
      Matrix.single_mul_mul_single, hTij]
  rw [hc1] at h1
  -- first arrow step, second coordinate: a one-row defect with zero diagonal
  have hZrow : IsRowSupported (Matrix.single j s b *
      (glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
        glMat (g * colUnitMat j x))) j := by
    intro p q hp
    rw [matrix_single_mul_apply, if_neg hp]
  have hZjj : (Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
      Matrix.single r i y * glMat (g * colUnitMat j x))) j j = 0 := by
    rw [matrix_single_mul_apply, if_pos rfl, hWcol s, mul_zero]
  have hZZ : Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
        Matrix.single r i y * glMat (g * colUnitMat j x)) *
      (Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
        Matrix.single r i y * glMat (g * colUnitMat j x))) = 0 :=
    IsRowSupported.mul_self hZrow hZjj
  have hWF : glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
      glMat (g * colUnitMat j x) * Matrix.single j s b = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = s
    · rw [if_pos hq, hWcol p, zero_mul]
    · rw [if_neg hq]
  have hc2 : ⁅elementaryUnit j s hjs b,
        ((g * colUnitMat j x)⁻¹ * elementaryUnit r i hri y *
          (g * colUnitMat j x) : (Matrix ι ι R)ˣ)⁆
      = sqZeroUnit (Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
          Matrix.single r i y * glMat (g * colUnitMat j x))) hZZ := by
    rw [hB1]
    apply Units.ext
    show (1 + Matrix.single j s b) *
        (1 + glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
          glMat (g * colUnitMat j x)) *
        (1 - Matrix.single j s b) *
        (1 - glMat ((g * colUnitMat j x)⁻¹) * Matrix.single r i y *
          glMat (g * colUnitMat j x))
      = 1 + Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
          Matrix.single r i y * glMat (g * colUnitMat j x))
    exact unipotent_commutator_of_right_annihilates _ _
      (single_mul_self_eq_zero j s hjs b) hWW hWF
  -- second arrow step: the junk coordinate dies, the good one gains `a`
  have h2 := hnorm.arrow_step_mem h1
    (elementaryUnit_mem r s hrs (y * x i * b))
    (elementaryUnit_mem j r hjr a)
  have hGZ : Matrix.single j r a *
      (Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
        Matrix.single r i y * glMat (g * colUnitMat j x))) = 0 := by
    ext p q
    rw [matrix_single_mul_apply, Matrix.zero_apply]
    by_cases hp : p = j
    · rw [if_pos hp, hZrow r q hrj, mul_zero]
    · rw [if_neg hp]
  have hZG : Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
        Matrix.single r i y * glMat (g * colUnitMat j x)) *
      Matrix.single j r a = 0 := by
    ext p q
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases hq : q = r
    · rw [if_pos hq]
      by_cases hp : p = j
      · rw [hp, hZjj, zero_mul]
      · rw [hZrow p j hp, zero_mul]
    · rw [if_neg hq]
  have hc3 : ⁅elementaryUnit j r hjr a,
      ⁅elementaryUnit j s hjs b, ((g * colUnitMat j x)⁻¹ *
        elementaryUnit r i hri y * (g * colUnitMat j x) :
          (Matrix ι ι R)ˣ)⁆⁆ = (1 : (Matrix ι ι R)ˣ) := by
    rw [hc2]
    apply Units.ext
    show (1 + Matrix.single j r a) *
        (1 + Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
          Matrix.single r i y * glMat (g * colUnitMat j x))) *
        (1 - Matrix.single j r a) *
        (1 - Matrix.single j s b * (glMat ((g * colUnitMat j x)⁻¹) *
          Matrix.single r i y * glMat (g * colUnitMat j x))) = 1
    rw [unipotent_commutator _ _ (single_mul_self_eq_zero j r hjr a) hZZ, hGZ,
      hZG]
    simp
  have hc4 : ⁅((elementaryUnit r s hrs (y * x i * b))⁻¹ : (Matrix ι ι R)ˣ),
        elementaryUnit j r hjr a⁆
      = elementaryUnit j s hjs (a * (y * x i * b)) := by
    rw [elementaryUnit_inv]
    apply Units.ext
    show (1 + Matrix.single r s (-(y * x i * b))) * (1 + Matrix.single j r a) *
        (1 - Matrix.single r s (-(y * x i * b))) * (1 - Matrix.single j r a)
      = 1 + Matrix.single j s (a * (y * x i * b))
    rw [unipotent_commutator_of_left_annihilates _ _
        (single_mul_self_eq_zero r s hrs (-(y * x i * b)))
        (single_mul_self_eq_zero j r hjr a)
        (Matrix.single_mul_single_of_ne (c := -(y * x i * b)) r s j hsj a),
      Matrix.single_mul_single_same, mul_neg, ← Matrix.single_neg,
      sub_neg_eq_add]
  rw [hc4, hc3, mul_one] at h2
  have hcoef : a * (y * x i * b) = a * y * x i * b := by
    rw [← mul_assoc, ← mul_assoc]
  rwa [hcoef] at h2

/-! ### Spreading one transvection over all positions -/

/-- **From one position to all positions.**  A subgroup normalized by
`EL_ι(R)` containing `t_{pq}(a c b)` for a fixed pair `p ≠ q` and *all* `a, b`
contains `t_{kl}(a c b)` for every pair `k ≠ l`.  Only the Steinberg relation
and a third index are used. -/
theorem elementaryUnit_mem_of_mem_spread (hcard : 3 ≤ Fintype.card ι)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R)) {c : R}
    {p q : ι} (hpq : p ≠ q)
    (hbase : ∀ a b : R, elementaryUnit p q hpq (a * c * b) ∈ H)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elementaryUnit k l hkl (a * c * b) ∈ H := by
  classical
  -- row `p`, arbitrary column
  have hrow : ∀ (m : ι) (hpm : p ≠ m) (a b : R),
      elementaryUnit p m hpm (a * c * b) ∈ H := by
    intro m hpm a b
    by_cases hmq : m = q
    · subst hmq
      exact hbase a b
    · have hqm : q ≠ m := fun h => hmq h.symm
      have hmem : ⁅elementaryUnit p q hpq (a * c * b),
          elementaryUnit q m hqm 1⁆ ∈ H :=
        hnorm.commutator_mem_left (hbase a b) (elementaryUnit_mem q m hqm 1)
      rw [elementaryUnit_commutator p q m hpq hqm hpm (a * c * b) 1,
        mul_one] at hmem
      exact hmem
  -- every position whose two indices avoid `p`
  have hgen : ∀ (u v : ι) (huv : u ≠ v), u ≠ p → p ≠ v → ∀ a b : R,
      elementaryUnit u v huv (a * c * b) ∈ H := by
    intro u v huv hup hpv a b
    have hmem : ⁅elementaryUnit u p hup a,
        elementaryUnit p v hpv (1 * c * b)⁆ ∈ H :=
      hnorm.commutator_mem_right (elementaryUnit_mem u p hup a)
        (hrow v hpv 1 b)
    rw [elementaryUnit_commutator u p v hup hpv huv a (1 * c * b), one_mul,
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
      have hmem : ⁅elementaryUnit k m hkm (a * c * b),
          elementaryUnit m l hml 1⁆ ∈ H :=
        hnorm.commutator_mem_left (hgen k m hkm hkp hpm a b)
          (elementaryUnit_mem m l hml 1)
      rw [elementaryUnit_commutator k m l hkm hml hkl (a * c * b) 1,
        mul_one] at hmem
      exact hmem
    · exact hgen k l hkl hkp hpl a b

/-! ### Preusser's Proposition 20 -/

/-- **Preusser, Proposition 20** (arXiv:1912.11386), in membership form, for a
subgroup of `GL_ι(R)` normalized by `EL_ι(R)`.

Let `H ≤ GL_ι(R)` be normalized by `EL_ι(R)` with `3 ≤ card ι`, let `g ∈ H`,
and let `x : ι → R` be a vector with `x j = 1` for some index `j`.  If `y`
annihilates the `i`-th coordinate of `g · x` on the left, then the elementary
transvection `t_{kl}(a y x_i b)` lies in `H`, for every `k ≠ l` and all
`a, b ∈ R`.

This is `RowAnnihilator.elGen_mem_of_row_annihilator` with the normal subgroup
of `EL_ι(R)` replaced by a subgroup of `GL_ι(R)` merely normalized by it, and
with `σ` allowed to be an arbitrary invertible matrix. -/
theorem elementaryUnit_mem_of_row_annihilator (hcard : 3 ≤ Fintype.card ι)
    {H : Subgroup (Matrix ι ι R)ˣ}
    (hnorm : NormalizedBy H (elementaryGroup ι R))
    {g : (Matrix ι ι R)ˣ} (hg : g ∈ H)
    (i j : ι) (x : ι → R) (y : R) (hxj : x j = 1)
    (hann : y * (∑ p, glMat g i p * x p) = 0)
    {k l : ι} (hkl : k ≠ l) (a b : R) :
    elementaryUnit k l hkl (a * y * x i * b) ∈ H := by
  classical
  obtain ⟨r, hri, hrj⟩ := exists_third_index hcard i j
  obtain ⟨s, hsr, hsj⟩ := exists_third_index hcard r j
  have hjs : j ≠ s := Ne.symm hsj
  have hrs : r ≠ s := Ne.symm hsr
  have hann' : y * glMat (g * colUnitMat j x) i j = 0 := by
    have he : glMat (g * colUnitMat j x) i j = ∑ p, glMat g i p * x p := by
      rw [glMat_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [glMat_colUnitMat_apply_col hxj p]
    rw [he]
    exact hann
  have hbase : ∀ a b : R,
      elementaryUnit j s hjs (a * (y * x i) * b) ∈ H := by
    intro a b
    have h := elementaryUnit_mem_of_column_annihilator hnorm hg hxj hann'
      hri hrj hjs hrs a b
    rwa [mul_assoc a y (x i)] at h
  rw [mul_assoc a y (x i)]
  exact elementaryUnit_mem_of_mem_spread hcard hnorm hjs hbase hkl a b

end PreusserNormalizedBy
end GroupApproximation
