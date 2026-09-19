import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKLocal

/-!
# vdK 3.9–3.10: `x(i, j)` does not depend on the zero of `j` used (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977),
3.9–3.10. For a row `j` with `j_r = j_s = 0` (`r ≠ s`) and `j i = 0`, the elements
`x(i, j) = x_r(i_r j) [x(i)_r, x_r(j)]` computed at `r` and at `s` agree (`xvw_indep`).

The proof follows vdK 3.9 with the roles of rows and columns exchanged, as vdK indicates for 3.10.
Write `i = i_r ε_r + i_s ε_s + l` with `l_r = l_s = 0`, and `y_r = [x(l)_r, x_r(j)]`.

* `commutator_x_rowProd`: `[x_sr(b), x_r(j)] = x_s(b j)`.
* `yEl_conj_rowProd`, `yEl_conj_colProd`: `y_r` is a product of generators avoiding row `s` and
  also one avoiding column `s`, with matrix `1 + l j`. By vdK's "well known fact" it commutes with
  `x_sr(c)`, `x_rs(c)`, `x(l)_s`, `x_s(j)`, and with `x_s(w)` whenever `w l = 0`.
* `wEl_conj_colProd`, `wEl_conj_rowProd`: the Weyl element `w_rs = x_rs(1) x_sr(-1) x_rs(1)` sends
  `x(l)_r` to `x(-l)_s` and `x_r(j)` to `x_s(-j)`.
* `yEl_eq_symm` (vdK 3.9): `y_r = y_s`. `y_r` commutes with `w_rs`, so
  `y_r = [x(l)_s⁻¹, x_s(j)⁻¹]`, and this equals `[x(l)_s, x_s(j)]` because `y_r` commutes with
  both entries.
* `xvw_indep`: `x(i, j)` at `r` is `x_r(i_r j) y x_s(i_s j)`, and at `s` it is
  `x_s(i_s j) y x_r(i_r j)`; the three factors commute pairwise.
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

theorem conj_fixed_symm {G : Type*} [Group G] {a b : G} (h : a * b * a⁻¹ = b) :
    b * a * b⁻¹ = a := by
  have h' : a * b = b * a := mul_inv_eq_iff_eq_mul.mp h
  rw [← h', mul_inv_cancel_right]

theorem commutator_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

/-- If `y = [a⁻¹, b⁻¹]` and `y` commutes with `a` and `b`, then `y = [a, b]`. -/
theorem eq_commutator_of_eq_commutator_inv {G : Type*} [Group G] {a b y : G}
    (hy : y = ⁅a⁻¹, b⁻¹⁆) (ha : a * y = y * a) (hb : b * y = y * b) : y = ⁅a, b⁆ := by
  have hab : a * b = b * a * y := by rw [hy, commutatorElement_def]; group
  have hya : y * a⁻¹ = a⁻¹ * y := by
    calc y * a⁻¹ = a⁻¹ * (a * y) * a⁻¹ := by group
      _ = a⁻¹ * (y * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * y := by group
  have hyb : y * b⁻¹ = b⁻¹ * y := by
    calc y * b⁻¹ = b⁻¹ * (b * y) * b⁻¹ := by group
      _ = b⁻¹ * (y * b) * b⁻¹ := by rw [hb]
      _ = b⁻¹ * y := by group
  symm
  calc ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := commutatorElement_def _ _
    _ = b * a * y * a⁻¹ * b⁻¹ := by rw [hab]
    _ = b * a * (y * a⁻¹) * b⁻¹ := by group
    _ = b * a * (a⁻¹ * y) * b⁻¹ := by rw [hya]
    _ = b * (y * b⁻¹) := by group
    _ = b * (b⁻¹ * y) := by rw [hyb]
    _ = y := by group

/-! ### Membership of row and column products in `colAvoid`, `rowAvoid` -/

/-- A map turning sums into products lands in `H` if it sends every `Pi.single q c` into `H`. -/
theorem mem_of_additive {H : Subgroup (SteinbergGroup I A)} {f : (I → A) → SteinbergGroup I A}
    (hf : ∀ u v, f (u + v) = f u * f v) (hs : ∀ (q : I) (c : A), f (Pi.single q c) ∈ H)
    (u : I → A) : f u ∈ H := by
  have hf0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := f 0) (by rw [mul_one]; exact h.symm)
  have key : ∀ S : Finset I, f (∑ q ∈ S, Pi.single q (u q)) ∈ H := by
    intro S
    refine Finset.induction_on S (by rw [Finset.sum_empty, hf0]; exact one_mem H) ?_
    intro q S hqS ih
    rw [Finset.sum_insert hqS, hf]
    exact mul_mem (hs q (u q)) ih
  have h := key Finset.univ
  rwa [Finset.univ_sum_single] at h

theorem rowProd_mem_colAvoid {r s : I} (hrs : r ≠ s) {j : I → A} (hjs : j s = 0) :
    rowProd r j ∈ colAvoid I A s := by
  have hnorm : rowProd r j = rowProd r (j - Pi.single s (j s)) := by
    rw [hjs, Pi.single_zero, sub_zero]
  rw [hnorm]
  refine mem_of_additive (f := fun u : I → A => rowProd r (u - Pi.single s (u s))) (fun u v => ?_)
    (fun q c => ?_) j
  · show rowProd r (u + v - Pi.single s ((u + v) s)) =
      rowProd r (u - Pi.single s (u s)) * rowProd r (v - Pi.single s (v s))
    rw [sub_single_add, rowProd_add]
  · show rowProd r (Pi.single q c - Pi.single s ((Pi.single q c : I → A) s)) ∈ colAvoid I A s
    by_cases hqs : q = s
    · subst hqs
      rw [Pi.single_eq_same, sub_self, rowProd_zero]
      exact one_mem _
    · rw [Pi.single_eq_of_ne (Ne.symm hqs), Pi.single_zero, sub_zero]
      by_cases hrq : r = q
      · subst hrq
        rw [rowProd_single_self]
        exact one_mem _
      · rw [rowProd_single_ne r q hrq]
        exact Subgroup.subset_closure ⟨r, q, hrq, c, hqs, rfl⟩

theorem rowProd_mem_rowAvoid {r s : I} (hrs : r ≠ s) (j : I → A) :
    rowProd r j ∈ rowAvoid I A s := by
  refine mem_of_additive (f := rowProd r) (fun u v => rowProd_add r u v) (fun q c => ?_) j
  by_cases hrq : r = q
  · subst hrq
    rw [rowProd_single_self]
    exact one_mem _
  · rw [rowProd_single_ne r q hrq]
    exact Subgroup.subset_closure ⟨r, q, hrq, c, hrs, rfl⟩

theorem colProd_mem_colAvoid {r s : I} (hrs : r ≠ s) (i : I → A) :
    colProd r i ∈ colAvoid I A s := by
  refine mem_of_additive (f := colProd r) (fun u v => colProd_add r u v) (fun p c => ?_) i
  by_cases hpr : p = r
  · subst hpr
    rw [colProd_single_self]
    exact one_mem _
  · rw [colProd_single_ne r p hpr]
    exact Subgroup.subset_closure ⟨p, r, hpr, c, hrs, rfl⟩

theorem colProd_mem_rowAvoid {r s : I} (hrs : r ≠ s) {i : I → A} (his : i s = 0) :
    colProd r i ∈ rowAvoid I A s := by
  have hnorm : colProd r i = colProd r (i - Pi.single s (i s)) := by
    rw [his, Pi.single_zero, sub_zero]
  rw [hnorm]
  refine mem_of_additive (f := fun u : I → A => colProd r (u - Pi.single s (u s))) (fun u v => ?_)
    (fun p c => ?_) i
  · show colProd r (u + v - Pi.single s ((u + v) s)) =
      colProd r (u - Pi.single s (u s)) * colProd r (v - Pi.single s (v s))
    rw [sub_single_add, colProd_add]
  · show colProd r (Pi.single p c - Pi.single s ((Pi.single p c : I → A) s)) ∈ rowAvoid I A s
    by_cases hps : p = s
    · subst hps
      rw [Pi.single_eq_same, sub_self, colProd_zero]
      exact one_mem _
    · rw [Pi.single_eq_of_ne (Ne.symm hps), Pi.single_zero, sub_zero]
      by_cases hpr : p = r
      · subst hpr
        rw [colProd_single_self]
        exact one_mem _
      · rw [colProd_single_ne r p hpr]
        exact Subgroup.subset_closure ⟨p, r, hpr, c, hps, rfl⟩

/-! ### Matrices from `stU` -/

theorem mat_eq_of_stU {z : SteinbergGroup I A} {v w : I → A} {h : w ⬝ᵥ v = 0}
    (hz : stU I A z = eUnit v w h) : mat z = 1 + Matrix.vecMulVec v w := by
  show ((stU I A z : (Matrix I I A)ˣ) : Matrix I I A) = _
  rw [hz]
  rfl

theorem matInv_eq_of_stU {z : SteinbergGroup I A} {v w : I → A} {h : w ⬝ᵥ v = 0}
    (hz : stU I A z = eUnit v w h) : matInv z = 1 - Matrix.vecMulVec v w := by
  show (((stU I A z)⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) = _
  rw [hz]
  rfl

theorem vecMul_one_sub_vecMulVec (u v w : I → A) :
    u ᵥ* (1 - Matrix.vecMulVec v w) = u - (u ⬝ᵥ v) • w := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]

theorem one_add_vecMulVec_mulVec (u v w : I → A) :
    (1 + Matrix.vecMulVec v w) *ᵥ u = u + (w ⬝ᵥ u) • v := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem xvw_of_apply_eq_zero {i j : I → A} {r : I} (hir : i r = 0) :
    xvw i j r = ⁅colProd r i, rowProd r j⁆ := by
  rw [xvw, hir, zero_smul, rowProd_zero, one_mul]

/-! ### The commutator `y = [x(l)_r, x_r(j)]` -/

/-- The hypotheses of vdK 3.9: `r ≠ s`, `l_r = l_s = 0`, `j_r = j_s = 0`, `j l = 0`. -/
def CommSetup (r s : I) (l j : I → A) : Prop :=
  r ≠ s ∧ l r = 0 ∧ l s = 0 ∧ j r = 0 ∧ j s = 0 ∧ j ⬝ᵥ l = 0

theorem CommSetup.symm {r s : I} {l j : I → A} (h : CommSetup r s l j) : CommSetup s r l j :=
  ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

/-- `y_r = [x(l)_r, x_r(j)]`. -/
def yEl (r : I) (l j : I → A) : SteinbergGroup I A :=
  ⁅colProd r l, rowProd r j⁆

theorem stU_yEl {r : I} {l j : I → A} (hjl : j ⬝ᵥ l = 0) (hlr : l r = 0) (hjr : j r = 0) :
    stU I A (yEl r l j) = eUnit l j hjl := by
  show stU I A ⁅colProd r l, rowProd r j⁆ = eUnit l j hjl
  rw [← xvw_of_apply_eq_zero (j := j) hlr]
  exact stU_xvw hjl hjr

/-- `y_r` commutes with `x_s(w)` when `w_s = 0` and `w l = 0`. -/
theorem yEl_conj_rowProd {r s : I} {l j : I → A} (h : CommSetup r s l j) {w : I → A}
    (hws : w s = 0) (hwl : w ⬝ᵥ l = 0) :
    yEl r l j * rowProd s w * (yEl r l j)⁻¹ = rowProd s w := by
  obtain ⟨hrs, hlr, _, hjr, hjs, hjl⟩ := h
  have hmem : yEl r l j ∈ colAvoid I A s :=
    commutator_mem_of_mem (colProd_mem_colAvoid hrs l) (rowProd_mem_colAvoid hrs hjs)
  rw [conj_rowProd hmem hws, matInv_eq_of_stU (stU_yEl hjl hlr hjr), vecMul_one_sub_vecMulVec, hwl,
    zero_smul, sub_zero]

/-- `y_r` commutes with `x(v)_s` when `v_s = 0` and `j v = 0`. -/
theorem yEl_conj_colProd {r s : I} {l j : I → A} (h : CommSetup r s l j) {v : I → A}
    (hvs : v s = 0) (hjv : j ⬝ᵥ v = 0) :
    yEl r l j * colProd s v * (yEl r l j)⁻¹ = colProd s v := by
  obtain ⟨hrs, hlr, hls, hjr, _, hjl⟩ := h
  have hmem : yEl r l j ∈ rowAvoid I A s :=
    commutator_mem_of_mem (colProd_mem_rowAvoid hrs hls) (rowProd_mem_rowAvoid hrs j)
  rw [conj_colProd hmem hvs, mat_eq_of_stU (stU_yEl hjl hlr hjr), one_add_vecMulVec_mulVec, hjv,
    zero_smul, add_zero]

theorem yEl_conj_x_sr {r s : I} {l j : I → A} (h : CommSetup r s l j) (c : A) :
    yEl r l j * x s r h.1.symm c * (yEl r l j)⁻¹ = x s r h.1.symm c := by
  have hc := yEl_conj_rowProd h (w := Pi.single r c) (Pi.single_eq_of_ne h.1.symm c)
    (by rw [single_dotProduct, h.2.1, mul_zero])
  rwa [rowProd_single_ne s r h.1.symm] at hc

theorem yEl_conj_x_rs {r s : I} {l j : I → A} (h : CommSetup r s l j) (c : A) :
    yEl r l j * x r s h.1 c * (yEl r l j)⁻¹ = x r s h.1 c := by
  have hc := yEl_conj_colProd h (v := Pi.single r c) (Pi.single_eq_of_ne h.1.symm c)
    (by rw [dotProduct_single, h.2.2.2.1, zero_mul])
  rwa [colProd_single_ne s r h.1 c] at hc

/-! ### Weyl elements -/

/-- `w_rs = x_rs(1) x_sr(-1) x_rs(1)`. -/
def wEl (r s : I) (hrs : r ≠ s) : SteinbergGroup I A :=
  x r s hrs 1 * x s r hrs.symm (-1) * x r s hrs 1

theorem wEl_conj_col {r s p : I} (hrs : r ≠ s) (hpr : p ≠ r) (hps : p ≠ s) (c : A) :
    wEl r s hrs * x p r hpr c * (wEl r s hrs)⁻¹ = x p s hps (-c) := by
  have hA : x r s hrs 1 * x p r hpr c * (x r s hrs 1)⁻¹ = x p r hpr c * x p s hps (-c) := by
    have h := x_conj_x_left r s p hrs hpr hps (1 : A) c
    rwa [mul_one] at h
  have hB1 : x s r hrs.symm (-1) * x p r hpr c * (x s r hrs.symm (-1))⁻¹ = x p r hpr c :=
    x_conj_x_of_commute hrs.symm hpr hpr.symm hrs (-1) c
  have hB2 : x s r hrs.symm (-1) * x p s hps (-c) * (x s r hrs.symm (-1))⁻¹ =
      x p s hps (-c) * x p r hpr (-c) := by
    have h := x_conj_x_left s r p hrs.symm hps hpr (-1 : A) (-c)
    rwa [show -(-c * -1 : A) = -c by ring] at h
  have hC : x p r hpr c * (x p s hps (-c) * x p r hpr (-c)) = x p s hps (-c) := by
    rw [← mul_assoc, (x_commute_of_ne p r p s hpr hps (Ne.symm hpr) (Ne.symm hps) c (-c)).eq,
      mul_assoc, x_mul, add_neg_cancel, x_zero, mul_one]
  have hA2 : x r s hrs 1 * x p s hps (-c) * (x r s hrs 1)⁻¹ = x p s hps (-c) :=
    x_conj_x_of_commute hrs hps hps.symm hrs.symm 1 (-c)
  calc wEl r s hrs * x p r hpr c * (wEl r s hrs)⁻¹
      = x r s hrs 1 * (x s r hrs.symm (-1) *
          (x r s hrs 1 * x p r hpr c * (x r s hrs 1)⁻¹) * (x s r hrs.symm (-1))⁻¹) *
            (x r s hrs 1)⁻¹ := by
        simp only [wEl]
        group
    _ = x r s hrs 1 * ((x s r hrs.symm (-1) * x p r hpr c * (x s r hrs.symm (-1))⁻¹) *
          (x s r hrs.symm (-1) * x p s hps (-c) * (x s r hrs.symm (-1))⁻¹)) *
            (x r s hrs 1)⁻¹ := by
        rw [hA]
        group
    _ = x r s hrs 1 * x p s hps (-c) * (x r s hrs 1)⁻¹ := by rw [hB1, hB2, hC]
    _ = x p s hps (-c) := hA2

theorem wEl_conj_row {r s q : I} (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q) (c : A) :
    wEl r s hrs * x r q hrq c * (wEl r s hrs)⁻¹ = x s q hsq (-c) := by
  have hA1 : x r s hrs 1 * x r q hrq c * (x r s hrs 1)⁻¹ = x r q hrq c :=
    x_conj_x_of_commute hrs hrq hrs.symm hrq.symm 1 c
  have hB : x s r hrs.symm (-1) * x r q hrq c * (x s r hrs.symm (-1))⁻¹ =
      x s q hsq (-1 * c) * x r q hrq c :=
    x_conj_x_right s r q hrs.symm hrq hsq (-1) c
  have hA2 : x r s hrs 1 * x s q hsq (-1 * c) * (x r s hrs 1)⁻¹ =
      x r q hrq (1 * (-1 * c)) * x s q hsq (-1 * c) :=
    x_conj_x_right r s q hrs hsq hrq 1 (-1 * c)
  have hC : x r q hrq (-c) * x s q hsq (-c) * x r q hrq c = x s q hsq (-c) := by
    rw [(x_commute_of_ne r q s q hrq hsq hsq.symm hrq.symm (-c) (-c)).eq, mul_assoc, x_mul,
      neg_add_cancel, x_zero, mul_one]
  calc wEl r s hrs * x r q hrq c * (wEl r s hrs)⁻¹
      = x r s hrs 1 * (x s r hrs.symm (-1) *
          (x r s hrs 1 * x r q hrq c * (x r s hrs 1)⁻¹) * (x s r hrs.symm (-1))⁻¹) *
            (x r s hrs 1)⁻¹ := by
        simp only [wEl]
        group
    _ = x r s hrs 1 * (x s q hsq (-1 * c) * x r q hrq c) * (x r s hrs 1)⁻¹ := by rw [hA1, hB]
    _ = (x r s hrs 1 * x s q hsq (-1 * c) * (x r s hrs 1)⁻¹) *
          (x r s hrs 1 * x r q hrq c * (x r s hrs 1)⁻¹) := by group
    _ = x r q hrq (1 * (-1 * c)) * x s q hsq (-1 * c) * x r q hrq c := by rw [hA2, hA1]
    _ = x s q hsq (-c) := by
        rw [show (1 : A) * (-1 * c) = -c by ring, show (-1 : A) * c = -c by ring]
        exact hC

/-- `u` with its `r`-th and `s`-th coordinates set to zero. -/
def norm2 (r s : I) (u : I → A) : I → A :=
  u - Pi.single r (u r) - Pi.single s (u s)

theorem norm2_add (r s : I) (u v : I → A) : norm2 r s (u + v) = norm2 r s u + norm2 r s v := by
  simp only [norm2, Pi.add_apply, Pi.single_add]
  abel

theorem norm2_single_left {r s : I} (hrs : r ≠ s) (c : A) :
    norm2 r s (Pi.single r c) = 0 := by
  rw [norm2, Pi.single_eq_same, Pi.single_eq_of_ne hrs.symm, Pi.single_zero, sub_self, sub_zero]

theorem norm2_single_right {r s : I} (hrs : r ≠ s) (c : A) :
    norm2 r s (Pi.single s c) = 0 := by
  rw [norm2, Pi.single_eq_same, Pi.single_eq_of_ne hrs, Pi.single_zero, sub_zero, sub_self]

theorem norm2_single_other {r s q : I} (hqr : q ≠ r) (hqs : q ≠ s) (c : A) :
    norm2 r s (Pi.single q c) = Pi.single q c := by
  rw [norm2, Pi.single_eq_of_ne hqr.symm, Pi.single_eq_of_ne hqs.symm, Pi.single_zero,
    Pi.single_zero, sub_zero, sub_zero]

theorem norm2_of {r s : I} {u : I → A} (hur : u r = 0) (hus : u s = 0) : norm2 r s u = u := by
  rw [norm2, hur, hus, Pi.single_zero, Pi.single_zero, sub_zero, sub_zero]

theorem colProd_neg (r : I) (i : I → A) : colProd r (-i) = (colProd r i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← colProd_add, add_neg_cancel, colProd_zero]

theorem rowProd_neg (r : I) (j : I → A) : rowProd r (-j) = (rowProd r j)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← rowProd_add, add_neg_cancel, rowProd_zero]

theorem wEl_conj_colProd {r s : I} (hrs : r ≠ s) {l : I → A} (hlr : l r = 0) (hls : l s = 0) :
    wEl r s hrs * colProd r l * (wEl r s hrs)⁻¹ = colProd s (-l) := by
  have key : ∀ u : I → A, wEl r s hrs * colProd r (norm2 r s u) * (wEl r s hrs)⁻¹ =
      colProd s (-norm2 r s u) := by
    refine eq_of_add_of_single
      (f := fun u : I → A => wEl r s hrs * colProd r (norm2 r s u) * (wEl r s hrs)⁻¹)
      (g := fun u : I → A => colProd s (-norm2 r s u)) (fun u v => ?_) (fun u v => ?_) (fun p c => ?_)
    · show wEl r s hrs * colProd r (norm2 r s (u + v)) * (wEl r s hrs)⁻¹ =
        wEl r s hrs * colProd r (norm2 r s u) * (wEl r s hrs)⁻¹ *
          (wEl r s hrs * colProd r (norm2 r s v) * (wEl r s hrs)⁻¹)
      rw [norm2_add, colProd_add]
      group
    · show colProd s (-norm2 r s (u + v)) = colProd s (-norm2 r s u) * colProd s (-norm2 r s v)
      rw [norm2_add, neg_add, colProd_add]
    · show wEl r s hrs * colProd r (norm2 r s (Pi.single p c)) * (wEl r s hrs)⁻¹ =
        colProd s (-norm2 r s (Pi.single p c))
      by_cases hpr : p = r
      · subst hpr
        rw [norm2_single_left hrs, colProd_zero, mul_one, mul_inv_cancel, neg_zero, colProd_zero]
      by_cases hps : p = s
      · subst hps
        rw [norm2_single_right hrs, colProd_zero, mul_one, mul_inv_cancel, neg_zero, colProd_zero]
      rw [norm2_single_other hpr hps, colProd_single_ne r p hpr, wEl_conj_col hrs hpr hps,
        ← Pi.single_neg, colProd_single_ne s p hps]
  have h := key l
  rwa [norm2_of hlr hls] at h

theorem wEl_conj_rowProd {r s : I} (hrs : r ≠ s) {j : I → A} (hjr : j r = 0) (hjs : j s = 0) :
    wEl r s hrs * rowProd r j * (wEl r s hrs)⁻¹ = rowProd s (-j) := by
  have key : ∀ u : I → A, wEl r s hrs * rowProd r (norm2 r s u) * (wEl r s hrs)⁻¹ =
      rowProd s (-norm2 r s u) := by
    refine eq_of_add_of_single
      (f := fun u : I → A => wEl r s hrs * rowProd r (norm2 r s u) * (wEl r s hrs)⁻¹)
      (g := fun u : I → A => rowProd s (-norm2 r s u)) (fun u v => ?_) (fun u v => ?_) (fun q c => ?_)
    · show wEl r s hrs * rowProd r (norm2 r s (u + v)) * (wEl r s hrs)⁻¹ =
        wEl r s hrs * rowProd r (norm2 r s u) * (wEl r s hrs)⁻¹ *
          (wEl r s hrs * rowProd r (norm2 r s v) * (wEl r s hrs)⁻¹)
      rw [norm2_add, rowProd_add]
      group
    · show rowProd s (-norm2 r s (u + v)) = rowProd s (-norm2 r s u) * rowProd s (-norm2 r s v)
      rw [norm2_add, neg_add, rowProd_add]
    · show wEl r s hrs * rowProd r (norm2 r s (Pi.single q c)) * (wEl r s hrs)⁻¹ =
        rowProd s (-norm2 r s (Pi.single q c))
      by_cases hqr : q = r
      · subst hqr
        rw [norm2_single_left hrs, rowProd_zero, mul_one, mul_inv_cancel, neg_zero, rowProd_zero]
      by_cases hqs : q = s
      · subst hqs
        rw [norm2_single_right hrs, rowProd_zero, mul_one, mul_inv_cancel, neg_zero, rowProd_zero]
      rw [norm2_single_other hqr hqs, rowProd_single_ne r q (Ne.symm hqr),
        wEl_conj_row hrs (Ne.symm hqr) (Ne.symm hqs), ← Pi.single_neg,
        rowProd_single_ne s q (Ne.symm hqs)]
  have h := key j
  rwa [norm2_of hjr hjs] at h

/-! ### vdK 3.9: `y_r = y_s` -/

/-- **vdK 3.9.** `[x(l)_r, x_r(j)] = [x(l)_s, x_s(j)]` when `l_r = l_s = j_r = j_s = 0` and
`j l = 0`. -/
theorem yEl_eq_symm {r s : I} {l j : I → A} (h : CommSetup r s l j) : yEl r l j = yEl s l j := by
  obtain ⟨hrs, hlr, hls, hjr, hjs, hjl⟩ := h
  have h' : CommSetup r s l j := ⟨hrs, hlr, hls, hjr, hjs, hjl⟩
  have hyw : yEl r l j * wEl r s hrs * (yEl r l j)⁻¹ = wEl r s hrs := by
    have e1 := yEl_conj_x_rs h' (1 : A)
    have e2 := yEl_conj_x_sr h' (-1 : A)
    calc yEl r l j * wEl r s hrs * (yEl r l j)⁻¹
        = (yEl r l j * x r s hrs 1 * (yEl r l j)⁻¹) *
            (yEl r l j * x s r hrs.symm (-1) * (yEl r l j)⁻¹) *
              (yEl r l j * x r s hrs 1 * (yEl r l j)⁻¹) := by
          simp only [wEl]
          group
      _ = wEl r s hrs := by rw [e1, e2]; rfl
  have hw : wEl r s hrs * yEl r l j * (wEl r s hrs)⁻¹ = yEl r l j := conj_fixed_symm hyw
  have hwy : wEl r s hrs * yEl r l j * (wEl r s hrs)⁻¹ =
      ⁅(colProd s l)⁻¹, (rowProd s j)⁻¹⁆ := by
    rw [← colProd_neg, ← rowProd_neg, ← wEl_conj_colProd hrs hlr hls,
      ← wEl_conj_rowProd hrs hjr hjs, yEl]
    simp only [commutatorElement_def]
    group
  have hy : yEl r l j = ⁅(colProd s l)⁻¹, (rowProd s j)⁻¹⁆ := hw.symm.trans hwy
  have ha : colProd s l * yEl r l j = yEl r l j * colProd s l :=
    (mul_inv_eq_iff_eq_mul.mp (yEl_conj_colProd h' hls hjl)).symm
  have hb : rowProd s j * yEl r l j = yEl r l j * rowProd s j :=
    (mul_inv_eq_iff_eq_mul.mp (yEl_conj_rowProd h' hjs hjl)).symm
  exact eq_commutator_of_eq_commutator_inv hy ha hb

#audit_axioms yEl_eq_symm

/-! ### `[x_sr(b), x_r(j)] = x_s(b j)` and commuting row products -/

/-- Row products for different rows commute when the vectors vanish at both rows. -/
theorem rowProd_commute_rowProd {r s : I} (hrs : r ≠ s) {u v : I → A} (hur : u r = 0)
    (hus : u s = 0) (hvr : v r = 0) : Commute (rowProd s v) (rowProd r u) := by
  have hz := rowProd_mem_colAvoid hrs.symm hvr
  have hc := conj_rowProd hz hur
  have hm : matInv (rowProd s v) =
      1 - Matrix.vecMulVec (Pi.single s (1 : A)) (v - Pi.single s (v s)) := by
    show (((stU I A (rowProd s v))⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) = _
    rw [stU_apply, mat_rowProd]
    rfl
  rw [hm, vecMul_one_sub_vecMulVec, dotProduct_single, hus, zero_mul, zero_smul, sub_zero] at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

theorem x_conj_rowProd {r s : I} (hrs : r ≠ s) (b : A) {j : I → A} (hjr : j r = 0)
    (hjs : j s = 0) :
    x s r hrs.symm b * rowProd r j * (x s r hrs.symm b)⁻¹ = rowProd s (b • j) * rowProd r j := by
  have key : ∀ u : I → A, x s r hrs.symm b * rowProd r (norm2 r s u) * (x s r hrs.symm b)⁻¹ =
      rowProd s (b • norm2 r s u) * rowProd r (norm2 r s u) := by
    refine eq_of_add_of_single
      (f := fun u : I → A => x s r hrs.symm b * rowProd r (norm2 r s u) * (x s r hrs.symm b)⁻¹)
      (g := fun u : I → A => rowProd s (b • norm2 r s u) * rowProd r (norm2 r s u))
      (fun u v => ?_) (fun u v => ?_) (fun q c => ?_)
    · show x s r hrs.symm b * rowProd r (norm2 r s (u + v)) * (x s r hrs.symm b)⁻¹ =
        x s r hrs.symm b * rowProd r (norm2 r s u) * (x s r hrs.symm b)⁻¹ *
          (x s r hrs.symm b * rowProd r (norm2 r s v) * (x s r hrs.symm b)⁻¹)
      rw [norm2_add, rowProd_add]
      group
    · show rowProd s (b • norm2 r s (u + v)) * rowProd r (norm2 r s (u + v)) =
        rowProd s (b • norm2 r s u) * rowProd r (norm2 r s u) *
          (rowProd s (b • norm2 r s v) * rowProd r (norm2 r s v))
      have hvr : (b • norm2 r s v) r = 0 := by
        rw [Pi.smul_apply, norm2, Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne hrs, sub_self, sub_zero, smul_zero]
      have hur : norm2 r s u r = 0 := by
        rw [norm2, Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hrs, sub_self,
          sub_zero]
      have hus : norm2 r s u s = 0 := by
        rw [norm2, Pi.sub_apply, Pi.sub_apply, Pi.single_eq_of_ne hrs.symm, Pi.single_eq_same,
          sub_zero, sub_self]
      have hcomm := (rowProd_commute_rowProd hrs hur hus hvr).eq
      rw [norm2_add, smul_add, rowProd_add, rowProd_add]
      calc rowProd s (b • norm2 r s u) * rowProd s (b • norm2 r s v) *
            (rowProd r (norm2 r s u) * rowProd r (norm2 r s v))
          = rowProd s (b • norm2 r s u) *
              (rowProd s (b • norm2 r s v) * rowProd r (norm2 r s u)) *
                rowProd r (norm2 r s v) := by group
        _ = rowProd s (b • norm2 r s u) *
              (rowProd r (norm2 r s u) * rowProd s (b • norm2 r s v)) *
                rowProd r (norm2 r s v) := by rw [hcomm]
        _ = rowProd s (b • norm2 r s u) * rowProd r (norm2 r s u) *
              (rowProd s (b • norm2 r s v) * rowProd r (norm2 r s v)) := by group
    · show x s r hrs.symm b * rowProd r (norm2 r s (Pi.single q c)) * (x s r hrs.symm b)⁻¹ =
        rowProd s (b • norm2 r s (Pi.single q c)) * rowProd r (norm2 r s (Pi.single q c))
      by_cases hqr : q = r
      · subst hqr
        rw [norm2_single_left hrs, rowProd_zero, mul_one, mul_inv_cancel, smul_zero, rowProd_zero,
          one_mul]
      by_cases hqs : q = s
      · subst hqs
        rw [norm2_single_right hrs, rowProd_zero, mul_one, mul_inv_cancel, smul_zero, rowProd_zero,
          one_mul]
      rw [norm2_single_other hqr hqs, rowProd_single_ne r q (Ne.symm hqr), ← Pi.single_smul',
        smul_eq_mul, rowProd_single_ne s q (Ne.symm hqs)]
      exact x_conj_x_right s r q hrs.symm (Ne.symm hqr) (Ne.symm hqs) b c
  have h := key j
  rwa [norm2_of hjr hjs] at h

/-- `[x_sr(b), x_r(j)] = x_s(b j)` when `j_r = j_s = 0`. -/
theorem commutator_x_rowProd {r s : I} (hrs : r ≠ s) (b : A) {j : I → A} (hjr : j r = 0)
    (hjs : j s = 0) : ⁅x s r hrs.symm b, rowProd r j⁆ = rowProd s (b • j) := by
  rw [commutatorElement_def, x_conj_rowProd hrs b hjr hjs, mul_inv_cancel_right]

/-! ### vdK 3.10: independence of the zero used -/

/-- `[x(i)_r, x_r(j)] = y_r x_s(i_s j)`, where `l = i - i_r ε_r - i_s ε_s`. -/
theorem commutator_colProd_rowProd_split {r s : I} {i j l : I → A}
    (hl : l = i - Pi.single r (i r) - Pi.single s (i s)) (h : CommSetup r s l j) :
    ⁅colProd r i, rowProd r j⁆ = yEl r l j * rowProd s (i s • j) := by
  obtain ⟨hrs, hlr, hls, hjr, hjs, hjl⟩ := h
  have h' : CommSetup r s l j := ⟨hrs, hlr, hls, hjr, hjs, hjl⟩
  have hi : i = Pi.single r (i r) + (Pi.single s (i s) + l) := by rw [hl]; abel
  have hcr : colProd r i = x s r hrs.symm (i s) * colProd r l := by
    conv_lhs => rw [hi]
    rw [colProd_add, colProd_add, colProd_single_self, one_mul, colProd_single_ne r s hrs.symm]
  have hgy : x s r hrs.symm (i s) * yEl r l j * (x s r hrs.symm (i s))⁻¹ = yEl r l j :=
    conj_fixed_symm (yEl_conj_x_sr h' (i s))
  calc ⁅colProd r i, rowProd r j⁆ = ⁅x s r hrs.symm (i s) * colProd r l, rowProd r j⁆ := by
        rw [hcr]
    _ = x s r hrs.symm (i s) * yEl r l j * (x s r hrs.symm (i s))⁻¹ *
          ⁅x s r hrs.symm (i s), rowProd r j⁆ := by
        rw [yEl]
        simp only [commutatorElement_def]
        group
    _ = yEl r l j * rowProd s (i s • j) := by rw [hgy, commutator_x_rowProd hrs (i s) hjr hjs]

/-- **vdK 3.10, independence of `r`.** If `j i = 0` and `j_r = j_s = 0`, then `x(i, j)` computed
at `r` equals `x(i, j)` computed at `s`. -/
theorem xvw_indep {i j : I → A} {r s : I} (hrs : r ≠ s) (hji : j ⬝ᵥ i = 0) (hjr : j r = 0)
    (hjs : j s = 0) : xvw i j r = xvw i j s := by
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
  have hl' : l = i - Pi.single s (i s) - Pi.single r (i r) := by rw [hl]; abel
  have hsplit_r := commutator_colProd_rowProd_split hl hS
  have hsplit_s := commutator_colProd_rowProd_split hl' hS.symm
  have hyy := yEl_eq_symm hS
  have hRr : (i r • j) r = 0 := by rw [Pi.smul_apply, hjr, smul_zero]
  have hRs : (i r • j) s = 0 := by rw [Pi.smul_apply, hjs, smul_zero]
  have hSr : (i s • j) r = 0 := by rw [Pi.smul_apply, hjr, smul_zero]
  have hSs : (i s • j) s = 0 := by rw [Pi.smul_apply, hjs, smul_zero]
  have hRl : (i r • j) ⬝ᵥ l = 0 := by rw [smul_dotProduct, hjl, smul_zero]
  have hSl : (i s • j) ⬝ᵥ l = 0 := by rw [smul_dotProduct, hjl, smul_zero]
  have hRS : rowProd r (i r • j) * rowProd s (i s • j) = rowProd s (i s • j) * rowProd r (i r • j) :=
    (rowProd_commute_rowProd hrs hRr hRs hSr).eq.symm
  have hYR : yEl r l j * rowProd r (i r • j) = rowProd r (i r • j) * yEl r l j := by
    have e := yEl_conj_rowProd hS.symm hRr hRl
    rw [← hyy] at e
    exact mul_inv_eq_iff_eq_mul.mp e
  have hYS : yEl r l j * rowProd s (i s • j) = rowProd s (i s • j) * yEl r l j :=
    mul_inv_eq_iff_eq_mul.mp (yEl_conj_rowProd hS hSs hSl)
  rw [xvw, xvw, hsplit_r, hsplit_s, ← hyy]
  calc rowProd r (i r • j) * (yEl r l j * rowProd s (i s • j))
      = (rowProd r (i r • j) * yEl r l j) * rowProd s (i s • j) := by group
    _ = (yEl r l j * rowProd r (i r • j)) * rowProd s (i s • j) := by rw [hYR]
    _ = yEl r l j * (rowProd r (i r • j) * rowProd s (i s • j)) := by group
    _ = yEl r l j * (rowProd s (i s • j) * rowProd r (i r • j)) := by rw [hRS]
    _ = (yEl r l j * rowProd s (i s • j)) * rowProd r (i r • j) := by group
    _ = (rowProd s (i s • j) * yEl r l j) * rowProd r (i r • j) := by rw [hYS]
    _ = rowProd s (i s • j) * (yEl r l j * rowProd r (i r • j)) := by group

#audit_axioms xvw_indep

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
