import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKRowCol

/-!
# vdK 3.10: the elements `x(i, j)` for a row with a zero (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977), 3.10.
For a column `i` (any column, not necessarily unimodular), a row `j` with `j i = 0`, and an index
`r` with `j_r = 0`, vdK sets `x(i, j) = x_r(i_r j) [x(i)_r, x_r(j)]`. This is Tulenbaev's
elementary `X(v, w) = X_r(v_r w) [X'_r(v), X_r(w)]`.

* `xvw i j r`: that element;
* `stU_xvw`: `π(x(i, j)) = e(i, j) = 1 + i j`, via `eUnit_commutator`:
  `[e(a, b), e(c, d)] = e((b c) a, d)` when `b a = d c = d a = 0`;
* `xvw_single_self`, `xvw_std`: `x(c ε_r, j) = x_r(c j)` and `x(ε_p, a ε_qᵀ) = x_pq(a)`
  (vdK's requirement 3.6 (d));
* `conj_xvw_of_avoid`: if `y` is a product of generators avoiding row `r` and a product of
  generators avoiding column `r` (for example `y = x_pq(a)` with `p, q ≠ r`), then
  `y x(i, j) y⁻¹ = x(π(y) i, j π(y)⁻¹)`, computed at the same `r` (part of vdK 3.12 and of
  Tulenbaev 1.1 (c)).

Still to do for vdK's Theorem 1: independence of `r` (vdK 3.9–3.10), the additivity lemma 3.11,
the remaining cases of 3.12, and 3.13–3.22.
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

variable (I A) in
/-- `π : St(n, A) → GL(n, A)`, as a homomorphism into the units. -/
def stU : SteinbergGroup I A →* (Matrix I I A)ˣ :=
  (elementaryGroup I A).subtype.comp projection

theorem stU_apply (z : SteinbergGroup I A) :
    stU I A z = ((projection z : elementaryGroup I A) : (Matrix I I A)ˣ) :=
  rfl

/-! ### Identities for `e(v, w)` -/

theorem eUnit_smul_swap (v w : I → A) (c : A) (h : (c • w) ⬝ᵥ v = 0) (h' : w ⬝ᵥ (c • v) = 0) :
    eUnit v (c • w) h = eUnit (c • v) w h' := by
  apply Units.ext
  change 1 + Matrix.vecMulVec v (c • w) = 1 + Matrix.vecMulVec (c • v) w
  rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]

theorem eUnit_comm_left (u v w : I → A) (hu : w ⬝ᵥ u = 0) (hv : w ⬝ᵥ v = 0) :
    eUnit u w hu * eUnit v w hv = eUnit v w hv * eUnit u w hu := by
  have huv : w ⬝ᵥ (u + v) = 0 := by rw [dotProduct_add, hu, hv, add_zero]
  have hvu : w ⬝ᵥ (v + u) = 0 := by rw [dotProduct_add, hu, hv, add_zero]
  rw [eUnit_mul_left u v w hu hv huv, eUnit_mul_left v u w hv hu hvu]
  exact eUnit_congr_left (add_comm u v) _ _

/-- `[e(a, b), e(c, d)] = e((b c) a, d)` when `b a = 0`, `d c = 0` and `d a = 0`. -/
theorem eUnit_commutator (a b c d : I → A) (hab : b ⬝ᵥ a = 0) (hcd : d ⬝ᵥ c = 0)
    (hda : d ⬝ᵥ a = 0) (h : d ⬝ᵥ ((b ⬝ᵥ c) • a) = 0) :
    ⁅eUnit a b hab, eUnit c d hcd⁆ = eUnit ((b ⬝ᵥ c) • a) d h := by
  have h'' : d ⬝ᵥ (c + (b ⬝ᵥ c) • a) = 0 := by rw [dotProduct_add, hcd, zero_add]; exact h
  have h' : (d - (d ⬝ᵥ a) • b) ⬝ᵥ (c + (b ⬝ᵥ c) • a) = 0 := by
    rw [hda, zero_smul, sub_zero]; exact h''
  have h1 : eUnit a b hab * eUnit c d hcd * (eUnit a b hab)⁻¹ =
      eUnit (c + (b ⬝ᵥ c) • a) d h'' := by
    refine (eUnit_conj (a, b) (c, d) hab hcd h').trans ?_
    exact eUnit_congr (by show d - (d ⬝ᵥ a) • b = d; rw [hda, zero_smul, sub_zero]) _ _
  have h2 : eUnit c d hcd * eUnit ((b ⬝ᵥ c) • a) d h = eUnit (c + (b ⬝ᵥ c) • a) d h'' :=
    eUnit_mul_left c _ d hcd h h''
  calc ⁅eUnit a b hab, eUnit c d hcd⁆
      = eUnit a b hab * eUnit c d hcd * (eUnit a b hab)⁻¹ * (eUnit c d hcd)⁻¹ :=
        commutatorElement_def _ _
    _ = eUnit c d hcd * eUnit ((b ⬝ᵥ c) • a) d h * (eUnit c d hcd)⁻¹ := by rw [h1, h2]
    _ = eUnit ((b ⬝ᵥ c) • a) d h := by
        rw [eUnit_comm_left c _ d hcd h, mul_inv_cancel_right]

#audit_axioms eUnit_commutator

/-- For `j_r = 0`, `x_r(j)` has matrix `e(ε_r, j)`. -/
theorem rowE_of_apply_eq_zero {r : I} {j : I → A} (hjr : j r = 0)
    (h : j ⬝ᵥ Pi.single r (1 : A) = 0) : rowE r j = eUnit (Pi.single r 1) j h :=
  eUnit_congr (by rw [hjr, Pi.single_zero, sub_zero]) _ _

/-! ### The elements `x(i, j)` -/

/-- **vdK 3.10.** `x(i, j) = x_r(i_r j) [x(i)_r, x_r(j)]`, meant for `j i = 0` and `j_r = 0`. -/
def xvw (i j : I → A) (r : I) : SteinbergGroup I A :=
  rowProd r (i r • j) * ⁅colProd r i, rowProd r j⁆

/-- **`π(x(i, j)) = e(i, j)`.** -/
theorem stU_xvw {i j : I → A} {r : I} (hji : j ⬝ᵥ i = 0) (hjr : j r = 0) :
    stU I A (xvw i j r) = eUnit i j hji := by
  have hjε : j ⬝ᵥ Pi.single r (1 : A) = 0 := by rw [dotProduct_single, hjr, zero_mul]
  have hcjε : (i r • j) ⬝ᵥ Pi.single r (1 : A) = 0 := by rw [smul_dotProduct, hjε, smul_zero]
  have hcjr : (i r • j) r = 0 := by rw [Pi.smul_apply, hjr, smul_zero]
  have hi'ε : Pi.single r (1 : A) ⬝ᵥ (i - Pi.single r (i r)) = 0 := single_dotProduct_sub_single r i
  have hji' : j ⬝ᵥ (i - Pi.single r (i r)) = 0 := by
    rw [dotProduct_sub, hji, dotProduct_single, hjr, zero_mul, sub_zero]
  have hεε : Pi.single r (1 : A) ⬝ᵥ Pi.single r (1 : A) = 1 := by
    rw [single_dotProduct, Pi.single_eq_same, mul_one]
  have hcomm : ⁅colE r i, rowE r j⁆ = eUnit (i - Pi.single r (i r)) j hji' := by
    rw [colE, rowE_of_apply_eq_zero hjr hjε,
      eUnit_commutator _ _ _ _ hi'ε hjε hji' (by rw [hεε, one_smul]; exact hji')]
    exact eUnit_congr_left (by rw [hεε, one_smul]) _ _
  have hsmul : j ⬝ᵥ (i r • Pi.single r (1 : A)) = 0 := by rw [dotProduct_smul, hjε, smul_zero]
  have hsum : j ⬝ᵥ (i r • Pi.single r (1 : A) + (i - Pi.single r (i r))) = 0 := by
    rw [dotProduct_add, hsmul, hji', add_zero]
  rw [xvw, map_mul, map_commutatorElement, stU_apply, stU_apply, stU_apply, mat_rowProd,
    mat_colProd, mat_rowProd, hcomm, rowE_of_apply_eq_zero hcjr hcjε,
    eUnit_smul_swap (Pi.single r 1) j (i r) hcjε hsmul,
    eUnit_mul_left _ _ j hsmul hji' hsum]
  refine eUnit_congr_left ?_ _ _
  rw [← Pi.single_smul', smul_eq_mul, mul_one, add_sub_cancel]

#audit_axioms stU_xvw

/-- `x(c ε_r, j) = x_r(c j)`: the commutator is trivial because `x(c ε_r)_r = 1`. -/
theorem xvw_single_self (r : I) (c : A) (j : I → A) :
    xvw (Pi.single r c) j r = rowProd r (c • j) := by
  rw [xvw, colProd_single_self, commutatorElement_one_left, mul_one, Pi.single_eq_same]

/-- **vdK's requirement 3.6 (d).** `x(ε_p, a ε_qᵀ) = x_pq(a)`, computed at `r = p`. -/
theorem xvw_std (p q : I) (hpq : p ≠ q) (a : A) :
    xvw (Pi.single p 1) (Pi.single q a) p = x p q hpq a := by
  rw [xvw_single_self, one_smul, rowProd_single_ne p q hpq]

#audit_axioms xvw_std

/-! ### Conjugation by elements avoiding row and column `r` -/

/-- **Conjugation (vdK 3.12, Tulenbaev 1.1 (c), the case avoiding `r`).** If `y` is both a
product of generators with row index `≠ r` and a product of generators with column index `≠ r`,
and `j_r = 0`, then `y x(i, j) y⁻¹ = x(π(y) i, j π(y)⁻¹)` at the same `r`. -/
theorem conj_xvw_of_avoid {r : I} {y : SteinbergGroup I A} (hy1 : y ∈ colAvoid I A r)
    (hy2 : y ∈ rowAvoid I A r) (i : I → A) {j : I → A} (hjr : j r = 0) :
    y * xvw i j r * y⁻¹ = xvw (mat y *ᵥ i) (j ᵥ* matInv y) r := by
  have hc := (rowConj_of_mem_colAvoid hy1).1
  have hr := (colConj_of_mem_rowAvoid hy2).1
  have hsingle : ∀ c : A, mat y *ᵥ Pi.single r c = Pi.single r c := by
    intro c
    rw [show Pi.single r c = c • Pi.single r (1 : A) by rw [← Pi.single_smul', smul_eq_mul, mul_one],
      Matrix.mulVec_smul, hc]
  have h1 : y * rowProd r (i r • j) * y⁻¹ = rowProd r ((i r • j) ᵥ* matInv y) :=
    conj_rowProd hy1 (by rw [Pi.smul_apply, hjr, smul_zero])
  have h2 : y * colProd r i * y⁻¹ = colProd r (mat y *ᵥ i) := by
    rw [← colProd_sub_single_self r i (i r),
      conj_colProd hy2 (i := i - Pi.single r (i r)) (by rw [Pi.sub_apply, Pi.single_eq_same, sub_self]),
      Matrix.mulVec_sub,
      hsingle, colProd_sub_single_self]
  have h3 : y * rowProd r j * y⁻¹ = rowProd r (j ᵥ* matInv y) := conj_rowProd hy1 hjr
  have hir : (mat y *ᵥ i) r = i r := mulVec_apply_of_single_vecMul hr i
  calc y * xvw i j r * y⁻¹
      = (y * rowProd r (i r • j) * y⁻¹) *
          ⁅y * colProd r i * y⁻¹, y * rowProd r j * y⁻¹⁆ := by
        rw [xvw]
        simp only [commutatorElement_def]
        group
    _ = xvw (mat y *ᵥ i) (j ᵥ* matInv y) r := by
        rw [h1, h2, h3, xvw, hir, Matrix.smul_vecMul]

#audit_axioms conj_xvw_of_avoid

/-- A generator `x_pq(a)` with `p, q ≠ r` avoids both row and column `r`. -/
theorem x_mem_colAvoid {r p q : I} (hpq : p ≠ q) (a : A) (hqr : q ≠ r) :
    x p q hpq a ∈ colAvoid I A r :=
  Subgroup.subset_closure ⟨p, q, hpq, a, hqr, rfl⟩

theorem x_mem_rowAvoid {r p q : I} (hpq : p ≠ q) (a : A) (hpr : p ≠ r) :
    x p q hpq a ∈ rowAvoid I A r :=
  Subgroup.subset_closure ⟨p, q, hpq, a, hpr, rfl⟩

/-- **Conjugation by a generator away from `r`.** For `p, q ≠ r` and `j_r = 0`,
`x_pq(a) x(i, j) x_pq(a)⁻¹ = x(i + a i_q ε_p, j - a j_p ε_qᵀ)` at the same `r`. -/
theorem conj_xvw_x {r p q : I} (hpq : p ≠ q) (a : A) (hpr : p ≠ r) (hqr : q ≠ r) (i : I → A)
    {j : I → A} (hjr : j r = 0) :
    x p q hpq a * xvw i j r * (x p q hpq a)⁻¹ =
      xvw ((1 + Matrix.single p q a) *ᵥ i) (j ᵥ* (1 - Matrix.single p q a)) r := by
  rw [conj_xvw_of_avoid (x_mem_colAvoid hpq a hqr) (x_mem_rowAvoid hpq a hpr) i hjr, mat_x,
    matInv_x]

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
