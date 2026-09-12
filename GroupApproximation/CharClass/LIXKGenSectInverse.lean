import GroupApproximation.CharClass.LIXKGenSect
import GroupApproximation.Meta.AxiomGuard

/-!
# `κ_j ∘ joinC k = id` on the open sector around the `j`-th zero

Lane `lix-oddside-n` (predecessor report `sp-oddside-n.md` §0.3a, test K3).

`CharClass/LIXKGenSect.lean` proves `joinC k ∘ κ_j = id` on all of `ℂ`.  The other composite
holds only on the open sector of half-width `π/(k+1)` around `kRoot k j`, and that is where the
chart at the `j`-th zero lives.  A point of the sector is written `r · exp(i(θ_j + t))` with
`r > 0`, `|t| < π/(k+1)`, `θ_j = π(2j+1)/(k+1)`; then

```text
joinC k z = r · exp(i(k+1)(θ_j + t)) = − r · exp(i(k+1)t) ,
arg (− joinC k z) = (k+1)·t ∈ (−π, π) ,
κ_j (joinC k z) = r · exp(i((k+1)t + π + 2πj)/(k+1)) = r · exp(i(θ_j + t)) = z .
```

The sector hypothesis is load-bearing: model test S4b (`nm/lixoddn/ksect_modeltest.py`) finds the
identity failing just outside it for every `k ≥ 1`, and a Euclidean ball of fixed radius is the
wrong hypothesis (it fails at `k ≥ 6`, predecessor report §0.3a).

## Main results

* `KGen.kZeroAngle`, `exp_kZeroAngle` — the centre angle, `exp(iθ_j) = kRoot k j`.
* `KGen.joinC_polar`, `neg_joinC_polar_zero`, `arg_neg_joinC_polar_zero`.
* `KGen.kSect_joinC_polar` — **`κ_j (joinC k z) = z` on the open sector.**
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.LIX.Powers

/-- The angle of the `j`-th zero, `π(2j+1)/(k+1)`. -/
def kZeroAngle (k : ℕ) (j : Fin (k + 1)) : ℝ :=
  Real.pi * (2 * ((j : ℕ) : ℝ) + 1) / ((k : ℝ) + 1)

/-- The centre of the sector is the `j`-th root. -/
theorem exp_kZeroAngle (k : ℕ) (j : Fin (k + 1)) :
    Complex.exp ((kZeroAngle k j : ℂ) * Complex.I) = kRoot k j := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [kRoot, kUnity, kBase, ← Complex.exp_nat_mul, ← Complex.exp_add, kZeroAngle]
  congr 1
  push_cast
  field_simp
  ring

/-- `joinC k` in polar coordinates. -/
theorem joinC_polar (k : ℕ) {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    joinC k ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp (((((k : ℝ) + 1) * φ : ℝ) : ℂ) * Complex.I) := by
  have hnorm : ‖(r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hr.le]
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hexp : ((k + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I)
      = ((((k : ℝ) + 1) * φ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [joinC, hnorm, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_pow, hexp, pow_succ,
    mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero k hr0)]

/-- On the sector around the `j`-th zero, `− joinC k z = r · exp(i(k+1)t)`. -/
theorem neg_joinC_polar_zero (k : ℕ) (j : Fin (k + 1)) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    -joinC k ((r : ℂ) * Complex.exp (((kZeroAngle k j + t : ℝ) : ℂ) * Complex.I))
      = (r : ℂ) * Complex.exp (((((k : ℝ) + 1) * t : ℝ) : ℂ) * Complex.I) := by
  have hkC : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [joinC_polar k hr]
  have hang : ((((k : ℝ) + 1) * (kZeroAngle k j + t) : ℝ) : ℂ) * Complex.I
      = (((((k : ℝ) + 1) * t : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I)
        + ((j : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [kZeroAngle]
    push_cast
    field_simp
    ring
  rw [hang, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I,
    Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  ring

/-- **The argument of `− joinC k z` on the sector is `(k+1)·t`.** -/
theorem arg_neg_joinC_polar_zero (k : ℕ) (j : Fin (k + 1)) {r t : ℝ} (hr : 0 < r)
    (ht : |t| < Real.pi / ((k : ℝ) + 1)) :
    Complex.arg
        (-joinC k ((r : ℂ) * Complex.exp (((kZeroAngle k j + t : ℝ) : ℂ) * Complex.I)))
      = ((k : ℝ) + 1) * t := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlt : |t| * ((k : ℝ) + 1) < Real.pi := (lt_div_iff₀ hk).mp ht
  have h1 : ((k : ℝ) + 1) * t ≤ ((k : ℝ) + 1) * |t| :=
    mul_le_mul_of_nonneg_left (le_abs_self t) hk.le
  have h2 : ((k : ℝ) + 1) * (-|t|) ≤ ((k : ℝ) + 1) * t :=
    mul_le_mul_of_nonneg_left (neg_abs_le t) hk.le
  rw [neg_joinC_polar_zero k j hr t, Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I,
    toIocMod_eq_self, Set.mem_Ioc]
  constructor <;> nlinarith [h1, h2, hlt]

/-- **`κ_j ∘ joinC k = id` on the open sector of half-width `π/(k+1)` around `kRoot k j`.** -/
theorem kSect_joinC_polar (k : ℕ) (j : Fin (k + 1)) {r t : ℝ} (hr : 0 < r)
    (ht : |t| < Real.pi / ((k : ℝ) + 1)) :
    kSect k j (joinC k ((r : ℂ) * Complex.exp (((kZeroAngle k j + t : ℝ) : ℂ) * Complex.I)))
      = (r : ℂ) * Complex.exp (((kZeroAngle k j + t : ℝ) : ℂ) * Complex.I) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hnorm : ‖(r : ℂ) * Complex.exp (((kZeroAngle k j + t : ℝ) : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hr.le]
  have hθ : kSectAngle k j
        (joinC k ((r : ℂ) * Complex.exp (((kZeroAngle k j + t : ℝ) : ℂ) * Complex.I)))
      = kZeroAngle k j + t := by
    rw [kSectAngle, arg_neg_joinC_polar_zero k j hr ht, kZeroAngle]
    field_simp
    ring
  rw [kSect, hθ, norm_joinC, hnorm]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.exp_kZeroAngle
#audit_axioms KGen.arg_neg_joinC_polar_zero
#audit_axioms KGen.kSect_joinC_polar

end GroupApproximation.CharClass
