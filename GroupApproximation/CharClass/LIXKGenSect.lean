import GroupApproximation.CharClass.LIXKMap
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import GroupApproximation.Meta.AxiomGuard

/-!
# The branches `κ_j` of the `(k+1)`-fold map, and `joinC k ∘ κ_j = id` everywhere

Lane `lix-oddside-n` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4; predecessor report
`notes/lix-stronger-lane-reports/sp-oddside-n.md` §0.3a).

`Powers.joinC k z = ‖z‖^{-k} z^{k+1}` has `k+1` preimages of `−1`, the roots `kRoot k j`.
The `k`-zero Step C reads the section in a chart at each of them, and the design of §0.3a
avoids differentiating `joinC k` altogether: chart the sphere at the `j`-th zero by the chart
at `−e₀` post-composed, in coordinate `0`, with the branch

```text
κ_j (w) = ‖w‖ · exp (i · (arg (−w) + π + 2πj) / (k+1)) ,
```

so that `Ψ_k ∘ chart_j` is the chart at `−e₀` itself and the section read in `chart_j` is the
same map at every `j`.

## What this file proves

* `kSect_pow` — `κ_j(w)^{k+1} = ‖w‖^k · w`, for **every** `w`.
* `joinC_kSect` — `joinC k (κ_j w) = w`, for **every** `w`, with no half-plane hypothesis.
  The predecessor's plan carried `w ≠ 0` and `arg (−w) ≠ π`; neither is used, because
  `‖x‖ · exp (arg x · i) = x` holds at every `x` including `0`.
* `kSect_neg_one` — `κ_j(−1) = kRoot k j`, so the chart at the `j`-th zero is centred there.
* `norm_kSect` — `κ_j` preserves the modulus.
* `continuousAt_kSect`, `continuousOn_kSect` — continuity wherever `−w` is in the slit plane,
  i.e. off the closed positive real ray.

The inverse half (`κ_j (joinC k z) = z` on the open sector of half-width `π/(k+1)` around
`kRoot k j`) is in `CharClass/LIXKGenSectInverse.lean`.

Model-tested before authoring (`nm/lixoddn/ksect_modeltest.py`, run on MSI acn112,
315 checks, 0 failures): S1 `joinC k ∘ κ_j = id` on random `w ∈ ℂ` including the real axis
of both signs and `0`, worst residual `3.8e−14`, `k ≤ 8`; S2 `κ_j(−1) = kUnity^j · kBase`;
S3 the modulus; S5 no jump above `1e−5` at step `1e−7` off the positive ray.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.LIX.Powers

/-- The angle of the `j`-th branch at `w`. -/
def kSectAngle (k : ℕ) (j : Fin (k + 1)) (w : ℂ) : ℝ :=
  (Complex.arg (-w) + Real.pi + 2 * Real.pi * ((j : ℕ) : ℝ)) / ((k : ℝ) + 1)

/-- **The `j`-th branch of the inverse of `joinC k`.** -/
def kSect (k : ℕ) (j : Fin (k + 1)) (w : ℂ) : ℂ :=
  (‖w‖ : ℂ) * Complex.exp ((kSectAngle k j w : ℂ) * Complex.I)

theorem norm_kSect (k : ℕ) (j : Fin (k + 1)) (w : ℂ) : ‖kSect k j w‖ = ‖w‖ := by
  rw [kSect, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_of_nonneg (norm_nonneg w)]

/-- `(k+1)` times the angle is `arg (−w) + π + 2πj`. -/
theorem natCast_mul_kSectAngle (k : ℕ) (j : Fin (k + 1)) (w : ℂ) :
    (((k + 1 : ℕ) : ℂ) * (kSectAngle k j w : ℂ))
      = (Complex.arg (-w) : ℂ) + (Real.pi : ℂ) + ((j : ℕ) : ℂ) * (2 * (Real.pi : ℂ)) := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [kSectAngle]
  push_cast
  field_simp
  ring

/-- **`κ_j(w)^{k+1} = ‖w‖^k · w`, at every `w`.** -/
theorem kSect_pow (k : ℕ) (j : Fin (k + 1)) (w : ℂ) :
    kSect k j w ^ (k + 1) = ((‖w‖ : ℝ) : ℂ) ^ k * w := by
  have hpolar : ((‖w‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (-w) : ℂ) * Complex.I) = -w := by
    have h := Complex.norm_mul_exp_arg_mul_I (-w)
    rwa [norm_neg] at h
  have hexp : Complex.exp ((kSectAngle k j w : ℂ) * Complex.I) ^ (k + 1)
      = -Complex.exp ((Complex.arg (-w) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← mul_assoc, natCast_mul_kSectAngle]
    have hsplit : ((Complex.arg (-w) : ℂ) + (Real.pi : ℂ) + ((j : ℕ) : ℂ) * (2 * (Real.pi : ℂ)))
          * Complex.I
        = ((Complex.arg (-w) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I)
          + ((j : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I,
      Complex.exp_nat_mul_two_pi_mul_I, mul_one, mul_neg_one]
  rw [kSect, mul_pow, hexp]
  linear_combination (-((‖w‖ : ℝ) : ℂ) ^ k) * hpolar

/-- **`joinC k ∘ κ_j = id`, at every `w`.** -/
theorem joinC_kSect (k : ℕ) (j : Fin (k + 1)) (w : ℂ) : joinC k (kSect k j w) = w := by
  rw [joinC, norm_kSect, kSect_pow, Complex.ofReal_pow]
  rcases eq_or_ne w 0 with h | h
  · subst h
    simp only [mul_zero]
  · have hn : ((‖w‖ : ℝ) : ℂ) ^ k ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))
    rw [inv_mul_cancel_left₀ hn]

/-- **The chart at the `j`-th zero is centred there**: `κ_j(−1) = kRoot k j`. -/
theorem kSect_neg_one (k : ℕ) (j : Fin (k + 1)) : kSect k j (-1) = kRoot k j := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [kSect, kSectAngle, kRoot, kUnity, kBase, neg_neg, Complex.arg_one, norm_neg, norm_one,
    Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- `κ_j` is continuous at every `w` whose negative lies in the slit plane. -/
theorem continuousAt_kSect (k : ℕ) (j : Fin (k + 1)) {w : ℂ}
    (hw : -w ∈ Complex.slitPlane) : ContinuousAt (kSect k j) w := by
  have harg : ContinuousAt (fun v : ℂ => Complex.arg (-v)) w :=
    (Complex.continuousAt_arg hw).comp (f := fun v : ℂ => -v) continuous_neg.continuousAt
  have hang : ContinuousAt (kSectAngle k j) w := by
    show ContinuousAt
      (fun v : ℂ => (Complex.arg (-v) + Real.pi + 2 * Real.pi * ((j : ℕ) : ℝ)) / ((k : ℝ) + 1)) w
    exact ((harg.add continuousAt_const).add continuousAt_const).div_const _
  have hexp : ContinuousAt
      (fun v : ℂ => Complex.exp ((kSectAngle k j v : ℂ) * Complex.I)) w :=
    Complex.continuous_exp.continuousAt.comp
      (f := fun v : ℂ => (kSectAngle k j v : ℂ) * Complex.I)
      ((Complex.continuous_ofReal.continuousAt.comp (f := kSectAngle k j) hang).mul
        continuousAt_const)
  have hnorm : ContinuousAt (fun v : ℂ => ((‖v‖ : ℝ) : ℂ)) w :=
    Complex.continuous_ofReal.continuousAt.comp (f := fun v : ℂ => ‖v‖)
      continuous_norm.continuousAt
  exact hnorm.mul hexp

/-- `κ_j` is continuous on the complement of the closed positive real ray. -/
theorem continuousOn_kSect (k : ℕ) (j : Fin (k + 1)) :
    ContinuousOn (kSect k j) {w : ℂ | -w ∈ Complex.slitPlane} :=
  fun _ hw => (continuousAt_kSect k j hw).continuousWithinAt

/-- `−1` is in the continuity domain, so the chart at the `j`-th zero sits inside it. -/
theorem neg_neg_one_mem_slitPlane : -(-1 : ℂ) ∈ Complex.slitPlane := by
  rw [neg_neg, Complex.mem_slitPlane_iff]
  left
  norm_num

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.kSect_pow
#audit_axioms KGen.joinC_kSect
#audit_axioms KGen.kSect_neg_one
#audit_axioms KGen.continuousOn_kSect

end GroupApproximation.CharClass
