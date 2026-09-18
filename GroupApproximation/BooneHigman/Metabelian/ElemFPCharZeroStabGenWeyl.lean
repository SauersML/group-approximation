import GroupApproximation.Steinberg.Basic
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugation by a Weyl-type element in a Steinberg group (lane bh-met-90d)

This holds over an arbitrary unital ring `R` and a finite index type `I`.  Fix `c ≠ L` in `I` and set
`w = x_{c,L}(1) · x_{L,c}(-1) · x_{c,L}(1)` (`czStabGen_weyl`).  For a root that avoids `c`,
conjugation by `w` acts as the transposition `c ↔ L` on the indices, with no signs:

* `czStabGen_weyl_conj_fix`: `w x_{p,q}(a) w⁻¹ = x_{p,q}(a)` when `p, q ∉ {c, L}`;
* `czStabGen_weyl_conj_row`: `w x_{L,q}(a) w⁻¹ = x_{c,q}(a)` when `q ∉ {c, L}`;
* `czStabGen_weyl_conj_col`: `w x_{p,L}(a) w⁻¹ = x_{p,c}(a)` when `p ∉ {c, L}`.

The proofs use only `x_mul`, `x_neg`, `x_commute_of_ne` and `x_commutator`.  They go through
the two conjugation identities `czStabGen_conj_left` and `czStabGen_conj_right`, which unfold
a commutator.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

/-- `⁅g, h⁆ = z` gives `g h g⁻¹ = z h`. -/
theorem czStabGen_conj_left {G : Type*} [Group G] {g h z : G} (hz : ⁅g, h⁆ = z) :
    g * h * g⁻¹ = z * h := by
  rw [← hz, commutatorElement_def, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_conj_left

/-- `⁅g, h⁆ = z` gives `h g h⁻¹ = z⁻¹ g`. -/
theorem czStabGen_conj_right {G : Type*} [Group G] {g h z : G} (hz : ⁅g, h⁆ = z) :
    h * g * h⁻¹ = z⁻¹ * g := by
  rw [← hz, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_conj_right

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- The Weyl-type element `x_{c,L}(1) x_{L,c}(-1) x_{c,L}(1)`. -/
def czStabGen_weyl (c L : I) (hcL : c ≠ L) : SteinbergGroup I R :=
  x c L hcL 1 * x L c hcL.symm (-1) * x c L hcL 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_weyl

/-- Conjugation by the Weyl element, factor by factor. -/
theorem czStabGen_weyl_conj (c L : I) (hcL : c ≠ L) (g : SteinbergGroup I R) :
    czStabGen_weyl c L hcL * g * (czStabGen_weyl c L hcL)⁻¹ =
      x c L hcL 1 * (x L c hcL.symm (-1) * (x c L hcL 1 * g * (x c L hcL 1)⁻¹) *
        (x L c hcL.symm (-1))⁻¹) * (x c L hcL 1)⁻¹ := by
  unfold czStabGen_weyl
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_weyl_conj

/-- Roots avoiding `c` and `L` are fixed. -/
theorem czStabGen_weyl_conj_fix (c L : I) (hcL : c ≠ L) {p q : I} (hpq : p ≠ q)
    (hpc : p ≠ c) (hqc : q ≠ c) (hpL : p ≠ L) (hqL : q ≠ L) (a : R) :
    czStabGen_weyl c L hcL * x p q hpq a * (czStabGen_weyl c L hcL)⁻¹ = x p q hpq a := by
  have s1 : x c L hcL 1 * x p q hpq a * (x c L hcL 1)⁻¹ = x p q hpq a := by
    rw [(x_commute_of_ne p q c L hpq hcL hqc hpL.symm a 1).symm.eq, mul_inv_cancel_right]
  have s2 : x L c hcL.symm (-1) * x p q hpq a * (x L c hcL.symm (-1))⁻¹ = x p q hpq a := by
    rw [(x_commute_of_ne p q L c hpq hcL.symm hqL hpc.symm a (-1)).symm.eq,
      mul_inv_cancel_right]
  rw [czStabGen_weyl_conj, s1, s2, s1]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_weyl_conj_fix

/-- `w x_{L,q}(a) w⁻¹ = x_{c,q}(a)` for `q ∉ {c, L}`. -/
theorem czStabGen_weyl_conj_row (c L : I) (hcL : c ≠ L) {q : I} (hLq : L ≠ q)
    (hqc : q ≠ c) (a : R) :
    czStabGen_weyl c L hcL * x L q hLq a * (czStabGen_weyl c L hcL)⁻¹ =
      x c q hqc.symm a := by
  have hcq : c ≠ q := hqc.symm
  have hqL : q ≠ L := hLq.symm
  have s1 : x c L hcL 1 * x L q hLq a * (x c L hcL 1)⁻¹ = x c q hcq a * x L q hLq a := by
    rw [czStabGen_conj_left (x_commutator c L q hcL hLq hcq 1 a), one_mul]
  have e1 : x L c hcL.symm (-1) * x c q hcq a * (x L c hcL.symm (-1))⁻¹ =
      x L q hLq ((-1) * a) * x c q hcq a :=
    czStabGen_conj_left (x_commutator L c q hcL.symm hcq hLq (-1) a)
  have e2 : x L c hcL.symm (-1) * x L q hLq a * (x L c hcL.symm (-1))⁻¹ = x L q hLq a := by
    rw [(x_commute_of_ne L c L q hcL.symm hLq hcL hqL (-1) a).eq, mul_inv_cancel_right]
  have e3 : x c q hcq a * x L q hLq a = x L q hLq a * x c q hcq a :=
    (x_commute_of_ne c q L q hcq hLq hqL hqc a a).eq
  have s2 : x L c hcL.symm (-1) * (x c q hcq a * x L q hLq a) * (x L c hcL.symm (-1))⁻¹ =
      x c q hcq a := by
    calc x L c hcL.symm (-1) * (x c q hcq a * x L q hLq a) * (x L c hcL.symm (-1))⁻¹
        = (x L c hcL.symm (-1) * x c q hcq a * (x L c hcL.symm (-1))⁻¹) *
            (x L c hcL.symm (-1) * x L q hLq a * (x L c hcL.symm (-1))⁻¹) := by group
      _ = x L q hLq ((-1) * a) * x c q hcq a * x L q hLq a := by rw [e1, e2]
      _ = x L q hLq ((-1) * a) * (x L q hLq a * x c q hcq a) := by rw [mul_assoc, e3]
      _ = x c q hcq a := by
        rw [← mul_assoc, x_mul, neg_one_mul, neg_add_cancel, x_zero, one_mul]
  have s3 : x c L hcL 1 * x c q hcq a * (x c L hcL 1)⁻¹ = x c q hcq a := by
    rw [(x_commute_of_ne c L c q hcL hcq hcL.symm hqc 1 a).eq, mul_inv_cancel_right]
  rw [czStabGen_weyl_conj, s1, s2, s3]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_weyl_conj_row

/-- `w x_{p,L}(a) w⁻¹ = x_{p,c}(a)` for `p ∉ {c, L}`. -/
theorem czStabGen_weyl_conj_col (c L : I) (hcL : c ≠ L) {p : I} (hpL : p ≠ L)
    (hpc : p ≠ c) (a : R) :
    czStabGen_weyl c L hcL * x p L hpL a * (czStabGen_weyl c L hcL)⁻¹ = x p c hpc a := by
  have s1 : x c L hcL 1 * x p L hpL a * (x c L hcL 1)⁻¹ = x p L hpL a := by
    rw [(x_commute_of_ne c L p L hcL hpL hpL.symm hcL.symm 1 a).eq, mul_inv_cancel_right]
  have s2 : x L c hcL.symm (-1) * x p L hpL a * (x L c hcL.symm (-1))⁻¹ =
      x p c hpc a * x p L hpL a := by
    rw [czStabGen_conj_right (x_commutator p L c hpL hcL.symm hpc a (-1)), ← x_neg,
      mul_neg_one, neg_neg]
  have e1 : x c L hcL 1 * x p c hpc a * (x c L hcL 1)⁻¹ =
      (x p L hpL (a * 1))⁻¹ * x p c hpc a :=
    czStabGen_conj_right (x_commutator p c L hpc hcL hpL a 1)
  have e3 : x p c hpc a * x p L hpL a = x p L hpL a * x p c hpc a :=
    (x_commute_of_ne p c p L hpc hpL hpc.symm hpL.symm a a).eq
  have s3 : x c L hcL 1 * (x p c hpc a * x p L hpL a) * (x c L hcL 1)⁻¹ = x p c hpc a := by
    calc x c L hcL 1 * (x p c hpc a * x p L hpL a) * (x c L hcL 1)⁻¹
        = (x c L hcL 1 * x p c hpc a * (x c L hcL 1)⁻¹) *
            (x c L hcL 1 * x p L hpL a * (x c L hcL 1)⁻¹) := by group
      _ = (x p L hpL (a * 1))⁻¹ * x p c hpc a * x p L hpL a := by rw [e1, s1]
      _ = (x p L hpL (a * 1))⁻¹ * (x p L hpL a * x p c hpc a) := by rw [mul_assoc, e3]
      _ = x p c hpc a := by rw [mul_one, inv_mul_cancel_left]
  rw [czStabGen_weyl_conj, s1, s2, s3]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_weyl_conj_col

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
