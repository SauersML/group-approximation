import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKConsist

/-!
# vdK 3.11–3.12: additivity and conjugation of `x(i, j)` (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977),
3.11–3.12, for an arbitrary column `i`.

* `xz i w`: `x(i, w)` computed at some zero of `w`. By `xz_eq` it equals `xvw i w t` at every
  zero `t` of `w` (vdK 3.10 consistency, `xvw_indep`).
* `commutator_mem_avoid`: if `j i = 0` and `j` vanishes at `r ≠ s`, then `[x(i)_r, x_r(j)]`
  avoids row `r` and column `r` ("can be written without column index `r`", vdK 3.11).
  `commutator_conj_rowProd` and `commutator_conj_colProd` give the commutations this implies.
* `xvw_add` (**vdK 3.11**): `x(i, j) x(i, k) = x(i, j + k)` when `j` and `k` have a common zero
  `p` and each has another zero. vdK asks for three distinct indices; the proof does not use
  `q ≠ r`.
* `xvw_add_col` (**vdK 3.11, columns**): `x(u, j) x(u', j) = x(u + u', j)` when `j` has two
  zeros.
* `conj_xz_x` (**vdK 3.12**): `x_pq(a) x(i, j) x_pq(a)⁻¹ = x(π(x_pq(a)) i, j π(x_pq(a))⁻¹)` when
  `j` has two zeros. The case `j_p = j_q = 0` is `conj_xvw_x_of_zeros`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement Matrix
open GroupApproximation.SteinbergGroup

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-! ### Group identities -/

theorem mul_commutator_aux {G : Type*} [Group G] {X B D P Q : G}
    (h1 : ⁅X, B⁆ * Q * ⁅X, B⁆⁻¹ = Q) (h2 : B * ⁅X, D⁆ * B⁻¹ = ⁅X, D⁆) :
    P * ⁅X, B⁆ * (Q * ⁅X, D⁆) = P * Q * ⁅X, B * D⁆ := by
  have e1 : ⁅X, B * D⁆ = ⁅X, B⁆ * (B * ⁅X, D⁆ * B⁻¹) := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅X, B⁆ * Q = Q * ⁅X, B⁆ := mul_inv_eq_iff_eq_mul.mp h1
  rw [e1, h2]
  calc P * ⁅X, B⁆ * (Q * ⁅X, D⁆) = P * (⁅X, B⁆ * Q) * ⁅X, D⁆ := by group
    _ = P * (Q * ⁅X, B⁆) * ⁅X, D⁆ := by rw [e2]
    _ = P * Q * (⁅X, B⁆ * ⁅X, D⁆) := by group

theorem mul_commutator_col_aux {G : Type*} [Group G] {X X' R P P' : G}
    (f1 : ⁅X', R⁆ * X * ⁅X', R⁆⁻¹ = X) (f2 : ⁅X, R⁆ * P' * ⁅X, R⁆⁻¹ = P')
    (f3 : ⁅X', R⁆ * R * ⁅X', R⁆⁻¹ = R) :
    P * ⁅X, R⁆ * (P' * ⁅X', R⁆) = P * P' * ⁅X * X', R⁆ := by
  have e1 : ⁅X * X', R⁆ = X * ⁅X', R⁆ * X⁻¹ * ⁅X, R⁆ := by
    simp only [commutatorElement_def]
    group
  have e2 : X * ⁅X', R⁆ * X⁻¹ = ⁅X', R⁆ := conj_fixed_symm f1
  have e3 : ⁅X', R⁆ * ⁅X, R⁆ * ⁅X', R⁆⁻¹ = ⁅X, R⁆ := by
    have h : ⁅X', R⁆ * ⁅X, R⁆ * ⁅X', R⁆⁻¹ =
        ⁅⁅X', R⁆ * X * ⁅X', R⁆⁻¹, ⁅X', R⁆ * R * ⁅X', R⁆⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h, f1, f3]
  have e2' : ⁅X, R⁆ * P' = P' * ⁅X, R⁆ := mul_inv_eq_iff_eq_mul.mp f2
  have e3' : ⁅X', R⁆ * ⁅X, R⁆ = ⁅X, R⁆ * ⁅X', R⁆ := mul_inv_eq_iff_eq_mul.mp e3
  rw [e1, e2]
  calc P * ⁅X, R⁆ * (P' * ⁅X', R⁆) = P * (⁅X, R⁆ * P') * ⁅X', R⁆ := by group
    _ = P * (P' * ⁅X, R⁆) * ⁅X', R⁆ := by rw [e2']
    _ = P * P' * (⁅X, R⁆ * ⁅X', R⁆) := by group
    _ = P * P' * (⁅X', R⁆ * ⁅X, R⁆) := by rw [e3']

theorem conj_aux {G : Type*} [Group G] {y X R P B Z : G} (hP : y * P * y⁻¹ = Z * P)
    (hX : y * X * y⁻¹ = X) (hR : y * R * y⁻¹ = B * R) (hXB : X * B * X⁻¹ = B)
    (hBC : B * ⁅X, R⁆ * B⁻¹ = ⁅X, R⁆) (hZP : Z * P = P * Z) :
    y * (P * ⁅X, R⁆) * y⁻¹ = P * (Z * ⁅X, R⁆) := by
  have e1 : y * (P * ⁅X, R⁆) * y⁻¹ = (y * P * y⁻¹) * ⁅y * X * y⁻¹, y * R * y⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅X, B * R⁆ = X * B * X⁻¹ * B⁻¹ * (B * ⁅X, R⁆ * B⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1, hP, hX, hR, e2, hXB, hBC, mul_inv_cancel, one_mul, hZP, mul_assoc]

/-! ### `x(i, w)` at any zero -/

open Classical in
/-- `x(i, w)` computed at some zero of `w` (vdK 3.10); `1` if `w` has no zero. By `xz_eq` the
choice of zero does not matter when `w i = 0`. -/
noncomputable def xz (i w : I → A) : SteinbergGroup I A :=
  if h : ∃ t, w t = 0 then xvw i w h.choose else 1

theorem xz_eq {i w : I → A} {t : I} (hwi : w ⬝ᵥ i = 0) (ht : w t = 0) : xz i w = xvw i w t := by
  have h : ∃ t, w t = 0 := ⟨t, ht⟩
  rw [xz, dif_pos h]
  by_cases hc : h.choose = t
  · rw [hc]
  · exact xvw_indep hc hwi h.choose_spec ht

theorem xvw_zero (i : I → A) (r : I) : xvw i 0 r = 1 := by
  rw [xvw, smul_zero, rowProd_zero, commutatorElement_one_right, one_mul]

theorem xz_zero (i : I → A) : xz i (0 : I → A) = 1 := by
  unfold xz
  by_cases h : ∃ t, (0 : I → A) t = 0
  · rw [dif_pos h, xvw_zero]
  · rw [dif_neg h]

theorem stU_xz {i w : I → A} {t : I} (hwi : w ⬝ᵥ i = 0) (ht : w t = 0) :
    stU I A (xz i w) = eUnit i w hwi := by
  rw [xz_eq hwi ht]
  exact stU_xvw hwi ht

/-! ### The commutator `[x(i)_r, x_r(j)]` -/

theorem dotProduct_sub_single_of {i j : I → A} {r : I} (hji : j ⬝ᵥ i = 0) (hjr : j r = 0) :
    j ⬝ᵥ (i - Pi.single r (i r)) = 0 := by
  rw [dotProduct_sub, hji, dotProduct_single, hjr, zero_mul, sub_zero]

/-- `π([x(i)_r, x_r(j)]) = e(i - i_r ε_r, j)`. -/
theorem stU_commutator {i j : I → A} {r : I} (hji : j ⬝ᵥ i = 0) (hjr : j r = 0) :
    stU I A ⁅colProd r i, rowProd r j⁆ =
      eUnit (i - Pi.single r (i r)) j (dotProduct_sub_single_of hji hjr) := by
  have h0 : (i - Pi.single r (i r)) r = 0 := by rw [Pi.sub_apply, Pi.single_eq_same, sub_self]
  rw [← colProd_sub_single_self r i (i r), ← xvw_of_apply_eq_zero (j := j) h0]
  exact stU_xvw (dotProduct_sub_single_of hji hjr) hjr

theorem mat_commutator {i j : I → A} {r : I} (hji : j ⬝ᵥ i = 0) (hjr : j r = 0) :
    mat ⁅colProd r i, rowProd r j⁆ = 1 + Matrix.vecMulVec (i - Pi.single r (i r)) j :=
  mat_eq_of_stU (stU_commutator hji hjr)

theorem matInv_commutator {i j : I → A} {r : I} (hji : j ⬝ᵥ i = 0) (hjr : j r = 0) :
    matInv ⁅colProd r i, rowProd r j⁆ = 1 - Matrix.vecMulVec (i - Pi.single r (i r)) j :=
  matInv_eq_of_stU (stU_commutator hji hjr)

/-- **vdK 3.11, the key observation.** If `j i = 0` and `j` vanishes at `r ≠ s`, then
`[x(i)_r, x_r(j)]` is a product of generators with column index `≠ r`, and also a product of
generators with row index `≠ r`. -/
theorem commutator_mem_avoid {i j : I → A} {r s : I} (hrs : r ≠ s) (hji : j ⬝ᵥ i = 0)
    (hjr : j r = 0) (hjs : j s = 0) :
    ⁅colProd r i, rowProd r j⁆ ∈ colAvoid I A r ∧ ⁅colProd r i, rowProd r j⁆ ∈ rowAvoid I A r := by
  obtain ⟨l, hl⟩ : ∃ l : I → A, l = i - Pi.single r (i r) - Pi.single s (i s) := ⟨_, rfl⟩
  have hlr : l r = 0 := by
    rw [hl, Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hrs, sub_self,
      sub_zero]
  have hls : l s = 0 := by
    rw [hl, Pi.sub_apply, Pi.sub_apply, Pi.single_eq_of_ne hrs.symm, Pi.single_eq_same, sub_zero,
      sub_self]
  have hjl : j ⬝ᵥ l = 0 := by
    rw [hl, dotProduct_sub, dotProduct_sub, hji, dotProduct_single, dotProduct_single, hjr, hjs,
      zero_mul, zero_mul, sub_zero, sub_zero]
  have hS : CommSetup r s l j := ⟨hrs, hlr, hls, hjr, hjs, hjl⟩
  have hs' : (i s • j) r = 0 := by rw [Pi.smul_apply, hjr, smul_zero]
  rw [commutator_colProd_rowProd_split hl hS, yEl_eq_symm hS]
  exact ⟨mul_mem (commutator_mem_of_mem (colProd_mem_colAvoid hrs.symm l)
      (rowProd_mem_colAvoid hrs.symm hjr)) (rowProd_mem_colAvoid hrs.symm hs'),
    mul_mem (commutator_mem_of_mem (colProd_mem_rowAvoid hrs.symm hlr)
      (rowProd_mem_rowAvoid hrs.symm j)) (rowProd_mem_rowAvoid hrs.symm _)⟩

/-- `[x(i)_r, x_r(j)]` commutes with `x_r(v)` when `v_r = 0` and `v i = 0`. -/
theorem commutator_conj_rowProd {i j : I → A} {r s : I} (hrs : r ≠ s) (hji : j ⬝ᵥ i = 0)
    (hjr : j r = 0) (hjs : j s = 0) {v : I → A} (hvr : v r = 0) (hvi : v ⬝ᵥ i = 0) :
    ⁅colProd r i, rowProd r j⁆ * rowProd r v * ⁅colProd r i, rowProd r j⁆⁻¹ = rowProd r v := by
  rw [conj_rowProd (commutator_mem_avoid hrs hji hjr hjs).1 hvr, matInv_commutator hji hjr,
    vecMul_one_sub_vecMulVec, dotProduct_sub, hvi, dotProduct_single, hvr, zero_mul, sub_self,
    zero_smul, sub_zero]

/-- `[x(i)_r, x_r(j)]` commutes with `x(w)_r` when `j w = 0`. -/
theorem commutator_conj_colProd {i j : I → A} {r s : I} (hrs : r ≠ s) (hji : j ⬝ᵥ i = 0)
    (hjr : j r = 0) (hjs : j s = 0) (w : I → A) (hjw : j ⬝ᵥ w = 0) :
    ⁅colProd r i, rowProd r j⁆ * colProd r w * ⁅colProd r i, rowProd r j⁆⁻¹ = colProd r w := by
  have h0 : (w - Pi.single r (w r)) r = 0 := by rw [Pi.sub_apply, Pi.single_eq_same, sub_self]
  rw [← colProd_sub_single_self r w (w r),
    conj_colProd (commutator_mem_avoid hrs hji hjr hjs).2 h0, mat_commutator hji hjr,
    one_add_vecMulVec_mulVec, dotProduct_sub, hjw, dotProduct_single, hjr, zero_mul, sub_self,
    zero_smul, add_zero]

/-! ### vdK 3.11: additivity -/

/-- **vdK 3.11.** If `j i = k i = 0`, `j_p = j_r = 0` and `k_p = k_q = 0` with `r, q ≠ p`, then
`x(i, j) x(i, k) = x(i, j + k)`, computed at the common zero `p`. -/
theorem xvw_add {i j k : I → A} {p q r : I} (hrp : r ≠ p) (hqp : q ≠ p) (hji : j ⬝ᵥ i = 0)
    (hki : k ⬝ᵥ i = 0) (hjp : j p = 0) (hjr : j r = 0) (hkp : k p = 0) (hkq : k q = 0) :
    xvw i j p * xvw i k p = xvw i (j + k) p := by
  have hC1 := commutator_conj_rowProd hrp.symm hji hjp hjr (v := i p • k)
    (by rw [Pi.smul_apply, hkp, smul_zero]) (by rw [smul_dotProduct, hki, smul_zero])
  have hC2 := commutator_conj_rowProd hqp.symm hki hkp hkq (v := j) hjp hji
  rw [xvw, xvw, xvw, smul_add, rowProd_add, rowProd_add]
  exact mul_commutator_aux hC1 (conj_fixed_symm hC2)

#audit_axioms xvw_add

/-- `xvw_add` for `xz`. -/
theorem xz_add {i j k : I → A} {p q r : I} (hrp : r ≠ p) (hqp : q ≠ p) (hji : j ⬝ᵥ i = 0)
    (hki : k ⬝ᵥ i = 0) (hjp : j p = 0) (hjr : j r = 0) (hkp : k p = 0) (hkq : k q = 0) :
    xz i j * xz i k = xz i (j + k) := by
  have hjki : (j + k) ⬝ᵥ i = 0 := by rw [add_dotProduct, hji, hki, add_zero]
  have hjkp : (j + k) p = 0 := by rw [Pi.add_apply, hjp, hkp, add_zero]
  rw [xz_eq hji hjp, xz_eq hki hkp, xz_eq hjki hjkp]
  exact xvw_add hrp hqp hji hki hjp hjr hkp hkq

/-- **vdK 3.11, rows and columns interchanged.** If `j` vanishes at `r ≠ s` and `j u = j u' = 0`,
then `x(u, j) x(u', j) = x(u + u', j)`. -/
theorem xvw_add_col {u u' j : I → A} {r s : I} (hrs : r ≠ s) (hju : j ⬝ᵥ u = 0)
    (hju' : j ⬝ᵥ u' = 0) (hjr : j r = 0) (hjs : j s = 0) :
    xvw u j r * xvw u' j r = xvw (u + u') j r := by
  have f1 := commutator_conj_colProd (i := u') hrs hju' hjr hjs u hju
  have f2 := commutator_conj_rowProd (i := u) hrs hju hjr hjs (v := u' r • j)
    (by rw [Pi.smul_apply, hjr, smul_zero]) (by rw [smul_dotProduct, hju, smul_zero])
  have f3 := commutator_conj_rowProd (i := u') hrs hju' hjr hjs (v := j) hjr hju'
  rw [xvw, xvw, xvw, Pi.add_apply, add_smul, rowProd_add, colProd_add]
  exact mul_commutator_col_aux f1 f2 f3

#audit_axioms xvw_add_col

theorem xz_add_col {u u' j : I → A} {r s : I} (hrs : r ≠ s) (hju : j ⬝ᵥ u = 0)
    (hju' : j ⬝ᵥ u' = 0) (hjr : j r = 0) (hjs : j s = 0) :
    xz u j * xz u' j = xz (u + u') j := by
  have hjuu : j ⬝ᵥ (u + u') = 0 := by rw [dotProduct_add, hju, hju', add_zero]
  rw [xz_eq hju hjr, xz_eq hju' hjr, xz_eq hjuu hjr]
  exact xvw_add_col hrs hju hju' hjr hjs

/-! ### vdK 3.12: conjugation by a generator -/

theorem one_add_single_mulVec (p q : I) (a : A) (i : I → A) :
    (1 + Matrix.single p q a) *ᵥ i = i + Pi.single p (i q * a) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, single_eq_vecMulVec_right, Matrix.vecMulVec_mulVec,
    single_dotProduct, one_mul, op_smul_eq_smul, ← Pi.single_smul', smul_eq_mul]

theorem vecMul_one_sub_single (p q : I) (a : A) (j : I → A) :
    j ᵥ* (1 - Matrix.single p q a) = j - Pi.single q (j p * a) := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, single_eq_vecMulVec_right, Matrix.vecMul_vecMulVec,
    dotProduct_single, ← Pi.single_smul', smul_eq_mul, mul_one]

theorem matInv_colProd (r : I) (i : I → A) :
    matInv (colProd r i) = 1 - Matrix.vecMulVec (i - Pi.single r (i r)) (Pi.single r 1) := by
  show (((stU I A (colProd r i))⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) = _
  rw [stU_apply, mat_colProd]
  rfl

/-- `x(i)_q` commutes with `x_p(v)` when `v_p = v_q = 0` and `v i = 0`. -/
theorem colProd_conj_rowProd {q p : I} (hqp : q ≠ p) (i : I → A) {v : I → A} (hvp : v p = 0)
    (hvq : v q = 0) (hvi : v ⬝ᵥ i = 0) :
    colProd q i * rowProd p v * (colProd q i)⁻¹ = rowProd p v := by
  rw [conj_rowProd (colProd_mem_colAvoid hqp i) hvp, matInv_colProd, vecMul_one_sub_vecMulVec,
    dotProduct_sub, hvi, dotProduct_single, hvq, zero_mul, sub_self, zero_smul, sub_zero]

/-- **vdK 3.12, the case `j_p = j_q = 0`.** Then
`x_pq(a) x(i, j) x_pq(a)⁻¹ = x(i + a i_q ε_p, j)`, computed at `q`. -/
theorem conj_xvw_x_of_zeros {p q : I} (hpq : p ≠ q) (a : A) {i j : I → A} (hji : j ⬝ᵥ i = 0)
    (hjp : j p = 0) (hjq : j q = 0) :
    x p q hpq a * xvw i j q * (x p q hpq a)⁻¹ = xvw (i + Pi.single p (i q * a)) j q := by
  have hqp : q ≠ p := hpq.symm
  have hPq : (i q • j) q = 0 := by rw [Pi.smul_apply, hjq, smul_zero]
  have hPp : (i q • j) p = 0 := by rw [Pi.smul_apply, hjp, smul_zero]
  have hP := x_conj_rowProd hqp a hPq hPp
  have hZ : a • i q • j = (i q * a) • j := by rw [smul_smul, mul_comm]
  rw [hZ] at hP
  have hR := x_conj_rowProd hqp a hjq hjp
  have hX : x p q hpq a * colProd q i * (x p q hpq a)⁻¹ = colProd q i := by
    rw [← colProd_single_ne q p hpq a, ← colProd_add, add_comm, colProd_add, mul_inv_cancel_right]
  have hvp : (a • j) p = 0 := by rw [Pi.smul_apply, hjp, smul_zero]
  have hvq : (a • j) q = 0 := by rw [Pi.smul_apply, hjq, smul_zero]
  have hvi : (a • j) ⬝ᵥ i = 0 := by rw [smul_dotProduct, hji, smul_zero]
  have hXB := colProd_conj_rowProd hqp i hvp hvq hvi
  have hBC : rowProd p (a • j) * ⁅colProd q i, rowProd q j⁆ * (rowProd p (a • j))⁻¹ =
      ⁅colProd q i, rowProd q j⁆ := by
    apply conj_fixed_symm
    rw [conj_rowProd (commutator_mem_of_mem (colProd_mem_colAvoid hqp i)
      (rowProd_mem_colAvoid hqp hjp)) hvp, matInv_commutator hji hjq, vecMul_one_sub_vecMulVec,
      dotProduct_sub, hvi, dotProduct_single, hvq, zero_mul, sub_self, zero_smul, sub_zero]
  have hZq : ((i q * a) • j) q = 0 := by rw [Pi.smul_apply, hjq, smul_zero]
  have hZp : ((i q * a) • j) p = 0 := by rw [Pi.smul_apply, hjp, smul_zero]
  have hZi : ((i q * a) • j) ⬝ᵥ i = 0 := by rw [smul_dotProduct, hji, smul_zero]
  have hZP : rowProd p ((i q * a) • j) * rowProd q (i q • j) =
      rowProd q (i q • j) * rowProd p ((i q * a) • j) :=
    (rowProd_commute_rowProd hqp hPq hPp hZq).eq
  have hE : ⁅x p q hpq (i q * a), rowProd q j⁆ = rowProd p ((i q * a) • j) :=
    commutator_x_rowProd hqp (i q * a) hjq hjp
  have hXZ := colProd_conj_rowProd hqp i hZp hZq hZi
  have hiq : (i + Pi.single p (i q * a)) q = i q := by
    rw [Pi.add_apply, Pi.single_eq_of_ne hqp, add_zero]
  have hcol : colProd q (i + Pi.single p (i q * a)) = colProd q i * x p q hpq (i q * a) := by
    rw [colProd_add, colProd_single_ne q p hpq]
  have e : ⁅colProd q i * x p q hpq (i q * a), rowProd q j⁆ =
      colProd q i * ⁅x p q hpq (i q * a), rowProd q j⁆ * (colProd q i)⁻¹ *
        ⁅colProd q i, rowProd q j⁆ := by
    simp only [commutatorElement_def]
    group
  rw [xvw, xvw, hiq, hcol, conj_aux hP hX hR hXB hBC hZP, e, hE, hXZ]

#audit_axioms conj_xvw_x_of_zeros

/-- **vdK 3.12.** If `j i = 0` and `j` vanishes at two indices, then
`x_pq(a) x(i, j) x_pq(a)⁻¹ = x(π(x_pq(a)) i, j π(x_pq(a))⁻¹)`. -/
theorem conj_xz_x {p q : I} (hpq : p ≠ q) (a : A) {i j : I → A} (hji : j ⬝ᵥ i = 0) {r s : I}
    (hrs : r ≠ s) (hjr : j r = 0) (hjs : j s = 0) :
    x p q hpq a * xz i j * (x p q hpq a)⁻¹ =
      xz ((1 + Matrix.single p q a) *ᵥ i) (j ᵥ* (1 - Matrix.single p q a)) := by
  by_cases h : ∃ t, j t = 0 ∧ t ≠ p ∧ t ≠ q
  · obtain ⟨t, hjt, htp, htq⟩ := h
    have hji' : (j ᵥ* (1 - Matrix.single p q a)) ⬝ᵥ ((1 + Matrix.single p q a) *ᵥ i) = 0 := by
      rw [vecMul_one_sub_single, one_add_single_mulVec, sub_dotProduct, dotProduct_add,
        dotProduct_add, hji, dotProduct_single, single_dotProduct, single_dotProduct,
        Pi.single_eq_of_ne hpq.symm]
      ring
    have hj't : (j ᵥ* (1 - Matrix.single p q a)) t = 0 := by
      rw [vecMul_one_sub_single, Pi.sub_apply, Pi.single_eq_of_ne htq, hjt, sub_zero]
    rw [xz_eq hji hjt, conj_xvw_x hpq a (Ne.symm htp) (Ne.symm htq) i hjt, xz_eq hji' hj't]
  · push_neg at h
    have hjpq : j p = 0 ∧ j q = 0 := by
      by_cases hrp : r = p
      · subst hrp
        have hsq : s = q := h s hjs (Ne.symm hrs)
        subst hsq
        exact ⟨hjr, hjs⟩
      · have hrq : r = q := h r hjr hrp
        subst hrq
        by_cases hsp : s = p
        · subst hsp
          exact ⟨hjs, hjr⟩
        · exact absurd (h s hjs hsp) (Ne.symm hrs)
    have hj' : j ᵥ* (1 - Matrix.single p q a) = j := by
      rw [vecMul_one_sub_single, hjpq.1, zero_mul, Pi.single_zero, sub_zero]
    have hji'' : j ⬝ᵥ (i + Pi.single p (i q * a)) = 0 := by
      rw [dotProduct_add, hji, dotProduct_single, hjpq.1, zero_mul, add_zero]
    rw [xz_eq hji hjpq.2, conj_xvw_x_of_zeros hpq a hji hjpq.1 hjpq.2, hj', one_add_single_mulVec,
      xz_eq hji'' hjpq.2]

#audit_axioms conj_xz_x

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
