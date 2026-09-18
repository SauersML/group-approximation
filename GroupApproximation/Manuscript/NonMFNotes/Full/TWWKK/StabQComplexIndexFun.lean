import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Reparametrisations of the spectrum of `(p - q)²`

The scalar half of the index of `qℂ` in Cuntz's picture of Kasparov theory (J. Cuntz, *A new look
at KK-theory*, K-Theory 1 (1987), Prop. 1.6 and §2; Blackadar, *K-Theory for Operator Algebras*,
17.3).  For the generating projections `p`, `q` of `qℂ` put `x = (p - q)²`; the element `q` is the
rotation of `p` by the functions `y(t) = t`, `k(t) = 1` of `x`.  A *reparametrisation* replaces
them by `y(t) = t A(t)`, `k(t) = √(A(t) B(t))` for continuous nonnegative `A`, `B` with
`t A(t) + (1 - t) B(t) = 1`; the key identity `k² · t(1 - t) = y(1 - y)` (`k_mul_self_mul`) is
exactly the hypothesis `k² Y² = y - y²` of `qIdx_proj_mul_self` once `Y² = x - x²`.

* `QReparam`, `QReparam.y`, `QReparam.k`, `QReparam.k_mul_self_mul`;
* `QReparam.std`: the trivial reparametrisation `A = B = 1` (`y = id`, `k = 1`);
* `QReparam.mix`: clamped convex combinations, jointly continuous in the parameter;
* `QReparam.adapted`: for `0 < a < b < 1`, a reparametrisation with `y = 0`, `k = 0` on `t ≤ a`
  and `y = 1`, `k = 0` on `t ≥ b`, so that the rotated projection becomes a spectral projection
  whenever `[a, b]` is a gap in the spectrum of `x`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C234, work order WO-TWWKK-C3: the index `HomotopyClass (Qalg ℂ) (Stab ℂ) ≃ ℤ`).
-/

namespace GroupApproximation.Full.TWWKK

noncomputable section

/-- A reparametrisation of the spectrum of `x = (p - q)²` in `qℂ`: continuous nonnegative
functions `A`, `B` with `t A(t) + (1 - t) B(t) = 1` (Cuntz 1987 §2;
`non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`). -/
structure QReparam where
  /-- the factor of `y(t) = t A(t)` -/
  A : ℝ → ℝ
  /-- the complementary factor, `1 - y(t) = (1 - t) B(t)` -/
  B : ℝ → ℝ
  continuous_A : Continuous A
  continuous_B : Continuous B
  nonneg_A : ∀ t, 0 ≤ A t
  nonneg_B : ∀ t, 0 ≤ B t
  sum_eq : ∀ t, t * A t + (1 - t) * B t = 1

namespace QReparam

variable (R : QReparam)

/-- The diagonal coefficient `y(t) = t A(t)` of the rotated projection. -/
def y (t : ℝ) : ℝ := t * R.A t

/-- The off-diagonal coefficient `k(t) = √(A(t) B(t))` of the rotated projection. -/
def k (t : ℝ) : ℝ := √(R.A t * R.B t)

theorem continuous_y : Continuous R.y :=
  show Continuous fun t => t * R.A t from continuous_id.mul R.continuous_A

theorem continuous_k : Continuous R.k :=
  show Continuous fun t => √(R.A t * R.B t) from (R.continuous_A.mul R.continuous_B).sqrt

theorem k_mul_self (t : ℝ) : R.k t * R.k t = R.A t * R.B t :=
  Real.mul_self_sqrt (mul_nonneg (R.nonneg_A t) (R.nonneg_B t))

/-- **The rotation identity** `k² · t(1 - t) = y(1 - y)`, the scalar form of the hypothesis
`k² Y² = y - y²` of `qIdx_proj_mul_self` (Cuntz 1987 §2; `non_mf_group_notes.tex`, UCT hypothesis
of `thm:fixed-radical-membership`). -/
theorem k_mul_self_mul (t : ℝ) : R.k t * R.k t * (t - t * t) = R.y t - R.y t * R.y t := by
  rw [R.k_mul_self]
  show R.A t * R.B t * (t - t * t) = t * R.A t - t * R.A t * (t * R.A t)
  linear_combination (t * R.A t) * R.sum_eq t

/-- The trivial reparametrisation `A = B = 1`: `y(t) = t`, `k(t) = 1`, rotating `p` onto `q`
itself. -/
def std : QReparam where
  A := fun _ => 1
  B := fun _ => 1
  continuous_A := continuous_const
  continuous_B := continuous_const
  nonneg_A := fun _ => show (0 : ℝ) ≤ 1 from zero_le_one
  nonneg_B := fun _ => show (0 : ℝ) ≤ 1 from zero_le_one
  sum_eq := fun t => show t * 1 + (1 - t) * 1 = 1 by ring

theorem std_y (t : ℝ) : std.y t = t := show t * 1 = t from mul_one t

theorem std_k (t : ℝ) : std.k t = 1 := by
  show √(1 * 1) = 1
  rw [mul_one, Real.sqrt_one]

/-- The clamped weight `max 0 (min 1 s) ∈ [0, 1]`. -/
def qClamp (s : ℝ) : ℝ := max 0 (min 1 s)

theorem qClamp_nonneg (s : ℝ) : 0 ≤ qClamp s := le_max_left _ _

theorem qClamp_le_one (s : ℝ) : qClamp s ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem continuous_qClamp : Continuous qClamp :=
  show Continuous fun s => max 0 (min 1 s) from continuous_const.max (continuous_const.min
    continuous_id)

theorem qClamp_zero : qClamp 0 = 0 := by
  show max 0 (min 1 0) = (0 : ℝ)
  rw [min_eq_right (zero_le_one : (0 : ℝ) ≤ 1), max_self]

theorem qClamp_one : qClamp 1 = 1 := by
  show max 0 (min 1 1) = (1 : ℝ)
  rw [min_self]
  exact max_eq_right zero_le_one

/-- The clamped convex combination of two reparametrisations; `s ↦ R.mix R' s` joins `R`
(`s ≤ 0`) to `R'` (`s ≥ 1`) (Cuntz 1987 §2; `non_mf_group_notes.tex`, UCT hypothesis of
`thm:fixed-radical-membership`). -/
def mix (R' : QReparam) (s : ℝ) : QReparam where
  A := fun t => (1 - qClamp s) * R.A t + qClamp s * R'.A t
  B := fun t => (1 - qClamp s) * R.B t + qClamp s * R'.B t
  continuous_A := (continuous_const.mul R.continuous_A).add (continuous_const.mul R'.continuous_A)
  continuous_B := (continuous_const.mul R.continuous_B).add (continuous_const.mul R'.continuous_B)
  nonneg_A := fun t => add_nonneg
    (mul_nonneg (sub_nonneg.mpr (qClamp_le_one s)) (R.nonneg_A t))
    (mul_nonneg (qClamp_nonneg s) (R'.nonneg_A t))
  nonneg_B := fun t => add_nonneg
    (mul_nonneg (sub_nonneg.mpr (qClamp_le_one s)) (R.nonneg_B t))
    (mul_nonneg (qClamp_nonneg s) (R'.nonneg_B t))
  sum_eq := fun t => by
    show t * ((1 - qClamp s) * R.A t + qClamp s * R'.A t) +
      (1 - t) * ((1 - qClamp s) * R.B t + qClamp s * R'.B t) = 1
    linear_combination (1 - qClamp s) * R.sum_eq t + qClamp s * R'.sum_eq t

variable (R' : QReparam)

theorem continuous_mix_A : Continuous fun st : ℝ × ℝ => (R.mix R' st.1).A st.2 := by
  show Continuous fun st : ℝ × ℝ => (1 - qClamp st.1) * R.A st.2 + qClamp st.1 * R'.A st.2
  have hc : Continuous fun st : ℝ × ℝ => qClamp st.1 := continuous_qClamp.comp continuous_fst
  exact ((continuous_const.sub hc).mul (R.continuous_A.comp continuous_snd)).add
    (hc.mul (R'.continuous_A.comp continuous_snd))

theorem continuous_mix_B : Continuous fun st : ℝ × ℝ => (R.mix R' st.1).B st.2 := by
  show Continuous fun st : ℝ × ℝ => (1 - qClamp st.1) * R.B st.2 + qClamp st.1 * R'.B st.2
  have hc : Continuous fun st : ℝ × ℝ => qClamp st.1 := continuous_qClamp.comp continuous_fst
  exact ((continuous_const.sub hc).mul (R.continuous_B.comp continuous_snd)).add
    (hc.mul (R'.continuous_B.comp continuous_snd))

/-- Joint continuity of the diagonal coefficient along a mix. -/
theorem continuous_mix_y : Continuous fun st : ℝ × ℝ => (R.mix R' st.1).y st.2 :=
  show Continuous fun st : ℝ × ℝ => st.2 * (R.mix R' st.1).A st.2 from
    continuous_snd.mul (R.continuous_mix_A R')

/-- Joint continuity of the off-diagonal coefficient along a mix. -/
theorem continuous_mix_k : Continuous fun st : ℝ × ℝ => (R.mix R' st.1).k st.2 :=
  show Continuous fun st : ℝ × ℝ => √((R.mix R' st.1).A st.2 * (R.mix R' st.1).B st.2) from
    ((R.continuous_mix_A R').mul (R.continuous_mix_B R')).sqrt

theorem mix_zero_A (t : ℝ) : (R.mix R' 0).A t = R.A t := by
  show (1 - qClamp 0) * R.A t + qClamp 0 * R'.A t = R.A t
  rw [qClamp_zero]
  ring

theorem mix_zero_B (t : ℝ) : (R.mix R' 0).B t = R.B t := by
  show (1 - qClamp 0) * R.B t + qClamp 0 * R'.B t = R.B t
  rw [qClamp_zero]
  ring

theorem mix_one_A (t : ℝ) : (R.mix R' 1).A t = R'.A t := by
  show (1 - qClamp 1) * R.A t + qClamp 1 * R'.A t = R'.A t
  rw [qClamp_one]
  ring

theorem mix_one_B (t : ℝ) : (R.mix R' 1).B t = R'.B t := by
  show (1 - qClamp 1) * R.B t + qClamp 1 * R'.B t = R'.B t
  rw [qClamp_one]
  ring

theorem mix_zero_y (t : ℝ) : (R.mix R' 0).y t = R.y t := by
  show t * (R.mix R' 0).A t = t * R.A t
  rw [mix_zero_A]

theorem mix_zero_k (t : ℝ) : (R.mix R' 0).k t = R.k t := by
  show √((R.mix R' 0).A t * (R.mix R' 0).B t) = √(R.A t * R.B t)
  rw [mix_zero_A, mix_zero_B]

theorem mix_one_y (t : ℝ) : (R.mix R' 1).y t = R'.y t := by
  show t * (R.mix R' 1).A t = t * R'.A t
  rw [mix_one_A]

theorem mix_one_k (t : ℝ) : (R.mix R' 1).k t = R'.k t := by
  show √((R.mix R' 1).A t * (R.mix R' 1).B t) = √(R'.A t * R'.B t)
  rw [mix_one_A, mix_one_B]

end QReparam

/-- The ramp `0` on `t ≤ a`, `1` on `t ≥ b`, affine in between. -/
def qRamp (a b t : ℝ) : ℝ := max 0 (min 1 ((t - a) / (b - a)))

theorem qRamp_nonneg (a b t : ℝ) : 0 ≤ qRamp a b t := le_max_left _ _

theorem qRamp_le_one (a b t : ℝ) : qRamp a b t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem continuous_qRamp (a b : ℝ) : Continuous (qRamp a b) :=
  show Continuous fun t => max 0 (min 1 ((t - a) / (b - a))) from
    continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const _))

theorem qRamp_of_le {a b t : ℝ} (hab : a < b) (ht : t ≤ a) : qRamp a b t = 0 := by
  have hu : (t - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le
  exact max_eq_left ((min_le_right _ _).trans hu)

theorem qRamp_of_ge {a b t : ℝ} (hab : a < b) (ht : b ≤ t) : qRamp a b t = 1 := by
  have hu : 1 ≤ (t - a) / (b - a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  show max 0 (min 1 ((t - a) / (b - a))) = 1
  rw [min_eq_left hu]
  exact max_eq_right zero_le_one

namespace QReparam

variable {a b : ℝ}

/-- **The reparametrisation adapted to `[a, b]`**, `0 < a < b < 1`: `A = φ / t`,
`B = (1 - φ) / (1 - t)` for the ramp `φ` from `a` to `b`.  Then `y = φ` on `t > 0`, and outside
`(a, b)` the rotated projection is diagonal (`k = 0`) with `y ∈ {0, 1}` (Cuntz 1987 §2;
Blackadar 17.3; `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`). -/
def adapted (ha : 0 < a) (hab : a < b) (hb : b < 1) : QReparam where
  A := fun t => qRamp a b t / t
  B := fun t => (1 - qRamp a b t) / (1 - t)
  continuous_A := continuous_iff_continuousAt.mpr fun t => by
    rcases lt_or_ge 0 t with ht | ht
    · exact (continuous_qRamp a b).continuousAt.div₀ continuousAt_id ht.ne'
    · have h : (fun s => qRamp a b s / s) =ᶠ[nhds t] fun _ => (0 : ℝ) :=
        (eventually_lt_nhds (ht.trans_lt ha)).mono fun s hs => by
          show qRamp a b s / s = 0
          rw [qRamp_of_le hab hs.le, zero_div]
      exact h.continuousAt
  continuous_B := continuous_iff_continuousAt.mpr fun t => by
    rcases lt_or_ge t 1 with ht | ht
    · exact (continuous_const.sub (continuous_qRamp a b)).continuousAt.div₀
        (continuous_const.sub continuous_id).continuousAt (sub_pos.mpr ht).ne'
    · have h : (fun s => (1 - qRamp a b s) / (1 - s)) =ᶠ[nhds t] fun _ => (0 : ℝ) :=
        (eventually_gt_nhds (hb.trans_le ht)).mono fun s hs => by
          show (1 - qRamp a b s) / (1 - s) = 0
          rw [qRamp_of_ge hab hs.le, sub_self, zero_div]
      exact h.continuousAt
  nonneg_A := fun t => by
    show 0 ≤ qRamp a b t / t
    rcases le_or_gt 0 t with ht | ht
    · exact div_nonneg (qRamp_nonneg a b t) ht
    · exact le_of_eq (by rw [qRamp_of_le hab (ht.le.trans ha.le), zero_div])
  nonneg_B := fun t => by
    show 0 ≤ (1 - qRamp a b t) / (1 - t)
    rcases le_or_gt t 1 with ht | ht
    · exact div_nonneg (sub_nonneg.mpr (qRamp_le_one a b t)) (sub_nonneg.mpr ht)
    · exact le_of_eq (by rw [qRamp_of_ge hab (hb.le.trans ht.le), sub_self, zero_div])
  sum_eq := fun t => by
    show t * (qRamp a b t / t) + (1 - t) * ((1 - qRamp a b t) / (1 - t)) = 1
    have h1 : t * (qRamp a b t / t) = qRamp a b t :=
      mul_div_cancel_of_imp' fun h => qRamp_of_le hab (h.le.trans ha.le)
    have h2 : (1 - t) * ((1 - qRamp a b t) / (1 - t)) = 1 - qRamp a b t :=
      mul_div_cancel_of_imp' fun h => by
        have hbt : b ≤ t := by linarith
        rw [qRamp_of_ge hab hbt, sub_self]
    rw [h1, h2]
    ring

variable (ha : 0 < a) (hab : a < b) (hb : b < 1)

theorem adapted_y_of_le {t : ℝ} (ht : t ≤ a) : (adapted ha hab hb).y t = 0 := by
  show t * (qRamp a b t / t) = 0
  rw [qRamp_of_le hab ht, zero_div, mul_zero]

theorem adapted_k_of_le {t : ℝ} (ht : t ≤ a) : (adapted ha hab hb).k t = 0 := by
  show √(qRamp a b t / t * ((1 - qRamp a b t) / (1 - t))) = 0
  rw [qRamp_of_le hab ht, zero_div, zero_mul, Real.sqrt_zero]

theorem adapted_y_of_ge {t : ℝ} (ht : b ≤ t) : (adapted ha hab hb).y t = 1 := by
  show t * (qRamp a b t / t) = 1
  rw [qRamp_of_ge hab ht, mul_div_cancel₀ 1 (ha.trans (hab.trans_le ht)).ne']

theorem adapted_k_of_ge {t : ℝ} (ht : b ≤ t) : (adapted ha hab hb).k t = 0 := by
  show √(qRamp a b t / t * ((1 - qRamp a b t) / (1 - t))) = 0
  rw [qRamp_of_ge hab ht, sub_self, zero_div, mul_zero, Real.sqrt_zero]

end QReparam

end

end GroupApproximation.Full.TWWKK
