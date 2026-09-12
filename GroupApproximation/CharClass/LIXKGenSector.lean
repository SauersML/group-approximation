import GroupApproximation.CharClass.LIXKGenSectInverse
import GroupApproximation.Meta.AxiomGuard

/-!
# The open sector around the `j`-th zero, and `κ_j`, `joinC k` as mutually inverse maps

Lane `lix-oddside-n` (predecessor report `sp-oddside-n.md` §0.3a).

The chart of `S^{2n+1}` at the `j`-th zero of the `k`-section is the chart at `−e₀`
post-composed, in coordinate `0`, with `κ_j`.  For that to be a homeomorphism onto an OPEN
neighbourhood, `κ_j` and `joinC k` must be mutually inverse between two open subsets of `ℂ`:

* `D := {w | −w ∈ slitPlane}` (off the closed positive real ray), where `κ_j` is continuous;
* `kSector k j`, the open sector of half-width `π/(k+1)` around `kRoot k j`, described as
  `{w | ρ_j w ∈ slitPlane ∧ |arg (ρ_j w)| < π/(k+1)}` with `ρ_j w = w · exp(−iθ_j)` the rotation
  carrying `kRoot k j` to `1`.

This description is open by inspection (`arg` is continuous on the slit plane), and the polar
form `w = ‖w‖ · exp(i(θ_j + arg (ρ_j w)))` converts membership into the hypothesis of
`LIXKGenSectInverse.kSect_joinC_polar`.

## Main results

* `KGen.kRotBack`, `KGen.kSector`, `isOpen_kSector`, `polar_of_mem_kSector`.
* `KGen.kSect_joinC_of_mem_kSector` — `κ_j (joinC k w) = w` on the sector.
* `KGen.neg_joinC_mem_slitPlane_of_mem_kSector` — `joinC k` maps the sector into `D`.
* `KGen.kSect_mem_kSector` — `κ_j` maps `D` into the sector.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.LIX.Powers

/-- The rotation carrying the `j`-th root to `1`. -/
def kRotBack (k : ℕ) (j : Fin (k + 1)) (w : ℂ) : ℂ :=
  w * Complex.exp (((-kZeroAngle k j : ℝ) : ℂ) * Complex.I)

theorem continuous_kRotBack (k : ℕ) (j : Fin (k + 1)) : Continuous (kRotBack k j) :=
  continuous_id.mul continuous_const

theorem norm_kRotBack (k : ℕ) (j : Fin (k + 1)) (w : ℂ) : ‖kRotBack k j w‖ = ‖w‖ := by
  rw [kRotBack, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `w = ρ_j(w) · exp(iθ_j)`. -/
theorem kRotBack_mul_exp (k : ℕ) (j : Fin (k + 1)) (w : ℂ) :
    kRotBack k j w * Complex.exp ((kZeroAngle k j : ℂ) * Complex.I) = w := by
  rw [kRotBack, mul_assoc, ← Complex.exp_add]
  have h0 : ((-kZeroAngle k j : ℝ) : ℂ) * Complex.I + (kZeroAngle k j : ℂ) * Complex.I = 0 := by
    push_cast
    ring
  rw [h0, Complex.exp_zero, mul_one]

/-- **The open sector of half-width `π/(k+1)` around `kRoot k j`.** -/
def kSector (k : ℕ) (j : Fin (k + 1)) : Set ℂ :=
  {w | kRotBack k j w ∈ Complex.slitPlane ∧
    |Complex.arg (kRotBack k j w)| < Real.pi / ((k : ℝ) + 1)}

theorem isOpen_kSector (k : ℕ) (j : Fin (k + 1)) : IsOpen (kSector k j) := by
  have hs : IsOpen (kRotBack k j ⁻¹' Complex.slitPlane) :=
    Complex.isOpen_slitPlane.preimage (continuous_kRotBack k j)
  have hf : ContinuousOn (fun w => |Complex.arg (kRotBack k j w)|)
      (kRotBack k j ⁻¹' Complex.slitPlane) :=
    continuous_abs.comp_continuousOn
      (Complex.continuousOn_arg.comp (continuous_kRotBack k j).continuousOn fun _ hw => hw)
  exact hf.isOpen_inter_preimage hs isOpen_Iio

theorem ne_zero_of_mem_kSector {k : ℕ} {j : Fin (k + 1)} {w : ℂ} (hw : w ∈ kSector k j) :
    w ≠ 0 := by
  intro h0
  have h := hw.1
  rw [h0, kRotBack, zero_mul] at h
  exact Complex.slitPlane_ne_zero h rfl

/-- **The polar form on the sector.** -/
theorem polar_of_mem_kSector {k : ℕ} {j : Fin (k + 1)} {w : ℂ} (_hw : w ∈ kSector k j) :
    w = ((‖w‖ : ℝ) : ℂ)
      * Complex.exp (((kZeroAngle k j + Complex.arg (kRotBack k j w) : ℝ) : ℂ) * Complex.I) := by
  have hpolar := Complex.norm_mul_exp_arg_mul_I (kRotBack k j w)
  rw [norm_kRotBack] at hpolar
  have hexp : Complex.exp (((kZeroAngle k j + Complex.arg (kRotBack k j w) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((Complex.arg (kRotBack k j w) : ℂ) * Complex.I)
        * Complex.exp ((kZeroAngle k j : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, ← mul_assoc, hpolar, kRotBack_mul_exp]

/-- **`κ_j ∘ joinC k = id` on the sector.** -/
theorem kSect_joinC_of_mem_kSector {k : ℕ} {j : Fin (k + 1)} {w : ℂ} (hw : w ∈ kSector k j) :
    kSect k j (joinC k w) = w := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr (ne_zero_of_mem_kSector hw)
  have h := kSect_joinC_polar k j hr hw.2
  rwa [← polar_of_mem_kSector hw] at h

/-- **`joinC k` carries the sector into the continuity domain of `κ_j`.** -/
theorem neg_joinC_mem_slitPlane_of_mem_kSector {k : ℕ} {j : Fin (k + 1)} {w : ℂ}
    (hw : w ∈ kSector k j) : -joinC k w ∈ Complex.slitPlane := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr (ne_zero_of_mem_kSector hw)
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have harg := arg_neg_joinC_polar_zero k j hr hw.2
  rw [← polar_of_mem_kSector hw] at harg
  rw [Complex.mem_slitPlane_iff_arg, harg]
  refine ⟨?_, ?_⟩
  · have hlt : |Complex.arg (kRotBack k j w)| * ((k : ℝ) + 1) < Real.pi :=
      (lt_div_iff₀ hk).mp hw.2
    have h1 : ((k : ℝ) + 1) * Complex.arg (kRotBack k j w)
        ≤ ((k : ℝ) + 1) * |Complex.arg (kRotBack k j w)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hk.le
    intro heq
    nlinarith [h1, hlt]
  · rw [neg_ne_zero]
    intro h0
    have hn := norm_joinC k w
    rw [h0, norm_zero] at hn
    exact (ne_zero_of_mem_kSector hw) (norm_eq_zero.mp hn.symm)

/-- **`κ_j` carries the continuity domain into the sector.** -/
theorem kSect_mem_kSector (k : ℕ) (j : Fin (k + 1)) {w : ℂ} (hw : -w ∈ Complex.slitPlane) :
    kSect k j w ∈ kSector k j := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkne : ((k : ℝ) + 1) ≠ 0 := hk.ne'
  have hkC : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, neg_zero] at hw
    exact Complex.slitPlane_ne_zero hw rfl
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hargpi : Complex.arg (-w) ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.mp hw).1
  have hle : Complex.arg (-w) ≤ Real.pi := Complex.arg_le_pi (-w)
  have hgt : -Real.pi < Complex.arg (-w) := Complex.neg_pi_lt_arg (-w)
  have hltpi : Complex.arg (-w) < Real.pi := lt_of_le_of_ne hle hargpi
  set a : ℝ := Complex.arg (-w) / ((k : ℝ) + 1) with ha
  have hrot : kRotBack k j (kSect k j w) = ((‖w‖ : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) := by
    rw [kRotBack, kSect, mul_assoc, ← Complex.exp_add]
    congr 2
    rw [kSectAngle, kZeroAngle, ha]
    push_cast
    field_simp
    ring
  have hapos : a * ((k : ℝ) + 1) = Complex.arg (-w) := by
    rw [ha]
    field_simp
  have habs : |a| < Real.pi / ((k : ℝ) + 1) := by
    rw [lt_div_iff₀ hk, ← abs_of_pos hk, ← abs_mul, hapos]
    exact abs_lt.mpr ⟨hgt, hltpi⟩
  have hamem : a ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [Set.mem_Ioc]
    have hpi : 0 < Real.pi := Real.pi_pos
    constructor
    · nlinarith [hapos, hgt, hk1]
    · nlinarith [hapos, hltpi, hk1]
  have harg : Complex.arg (kRotBack k j (kSect k j w)) = a := by
    rw [hrot, Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I, toIocMod_eq_self]
    exact hamem
  refine ⟨?_, ?_⟩
  · rw [Complex.mem_slitPlane_iff_arg, harg]
    refine ⟨?_, ?_⟩
    · intro heq
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [hapos, hltpi, hk1, heq]
    · rw [hrot]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _)
  · rw [harg]
    exact habs

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.isOpen_kSector
#audit_axioms KGen.kSect_joinC_of_mem_kSector
#audit_axioms KGen.neg_joinC_mem_slitPlane_of_mem_kSector
#audit_axioms KGen.kSect_mem_kSector

end GroupApproximation.CharClass
