import GroupApproximation.Analysis.LIXPowersJoinPower
import GroupApproximation.Analysis.LIXPowersEH
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The angle reparametrisation family for the join power

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3 item 1, concrete half.
`Analysis/LIXPowersEH.lean` reduces `u^k ≃ u ∘ ψ_k` to a *choice*: a family
`P : ℕ → ℝ → E → E` of self-maps of the closed ball, continuous in `(θ, y)`, with
`P j 0 = id`, together with the identification `∏_{j} (u ∘ P j 1) = u ∘ ψ_k`.  This file
builds that family for the agreed `ψ_k`, the join power of
`Analysis/LIXPowersJoinPower.lean`.

## The family

In the complex coordinate `z` of the rotation plane, with `φ = arg z`, the `j`-th factor
of the `k+1` is

```text
A_{j,θ} (z, v) = (|z| · exp (i · c_{j,θ}(φ)),  v)
c_{j,θ}(φ)     = clamp ((1 + θ k)(φ + π) − 2π θ j, 0, 2π) − π
```

At `θ = 0` this is the identity (`clamp` is inactive because `φ + π ∈ (0, 2π]`), and at
`θ = 1` the `j`-th factor stretches the `j`-th angular slab over the whole circle and sends
everything outside it to the **wall**, the non-positive real axis of the plane.

## Why the angle, and not a suspension coordinate

A `k`-fold pinch needs the two ends of its pinch interval to be identified.  In a
suspension coordinate they are the two poles, which are different points, so the assembled
pinch is discontinuous and only its composite with a based `u` is a map.  In the *angle*
coordinate the two ends are the same set -- here `φ = π` and `φ = −π` are both the negative
real axis -- so every `A_{j,θ}` is an honest continuous self-map of `E` and no gluing of
matrix-valued products is ever needed.  That is the whole reason this lane recommends the
join power.

Mathlib's `Complex.arg` has its cut on the non-positive reals, which is exactly where the
clamp saturates, so the cut costs one lemma rather than a change of coordinates: at a
negative real `z₀` the two one-sided limits of `arg` are `π` and `−π`, the clamp is
saturated at both, and `exp (iπ) = exp (−iπ) = −1`, so `angleC` is continuous there with
value `−‖z₀‖`.  `continuous_angleC` is that argument.

## The wall, and the basepoint condition

`wallRetract e₁ e₂ (z, v) = (−|z|, v)` is a *radial* retraction of `E` onto the wall.  Off
its own slab, `A_{j,1}` is literally `wallRetract` (`angleRepar_eq_wallRetract`), so the
basepoint condition that collapses the ordered product to a single composite is

```text
∀ y, ‖y‖ ≤ 1 → W (wallRetract e₁ e₂ y) = 1
```

`sp-design`'s §2.4(a) states the same condition for the *positive* real axis, because their
angle runs in `[0, 2π)`; the two differ by the rotation `z ↦ −z` of the plane, and their
retraction `x ↦ (|x₀|, x₁, …)` becomes `x ↦ (−|x₀|, x₁, …)` here.  Nothing else changes.

## What this file does not do

The slab arithmetic -- choosing the index `i` with `(k+1)(φ+π) ∈ [2πi, 2π(i+1)]` and
checking that the other `k` factors saturate -- is the remaining step, and it is deliberately
in a separate file so that a failure in its real-arithmetic bookkeeping cannot redden this
one.  The two lemmas it consumes from here are `angleParam_eq_pi_of_le` and
`angleParam_eq_neg_pi_of_le`; the target it must hit is `Powers.PinchIdentification`.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The clamped angle -/

section AngleParam

/-- The homotopy parameter, clamped to `[0, 1]`.  Clamping inside the definition is what
makes `angleParam` continuous in `(θ, φ)` for *every* real `θ`: for `θ < 0` the two ends of
the clamp would no longer both saturate, and the map would be discontinuous across the
cut. -/
def angleClamp (θ : ℝ) : ℝ := min 1 (max 0 θ)

theorem angleClamp_nonneg (θ : ℝ) : 0 ≤ angleClamp θ :=
  le_min (by norm_num) (le_max_left _ _)

theorem angleClamp_le_one (θ : ℝ) : angleClamp θ ≤ 1 := min_le_left _ _

theorem angleClamp_zero : angleClamp 0 = 0 := by
  rw [angleClamp, max_self, min_eq_right (by norm_num)]

theorem angleClamp_one : angleClamp 1 = 1 := by
  rw [angleClamp, max_eq_right (by norm_num), min_self]

theorem continuous_angleClamp : Continuous angleClamp :=
  continuous_const.min (continuous_const.max continuous_id)

/-- The raw (unclamped) pinch coordinate of the `j`-th factor, out of `k + 1`. -/
def angleRaw (k j : ℕ) (θ φ : ℝ) : ℝ :=
  (1 + angleClamp θ * k) * (φ + Real.pi) - 2 * Real.pi * angleClamp θ * j

/-- **The clamped angle.**  `angleParam k j θ φ` is the reparametrised angle of the `j`-th
of `k + 1` factors at time `θ`. -/
def angleParam (k j : ℕ) (θ φ : ℝ) : ℝ :=
  min (2 * Real.pi) (max 0 (angleRaw k j θ φ)) - Real.pi

theorem continuous_angleRaw (k j : ℕ) :
    Continuous fun q : ℝ × ℝ => angleRaw k j q.1 q.2 := by
  refine Continuous.sub ?_ ?_
  · exact ((continuous_const.add
      ((continuous_angleClamp.comp continuous_fst).mul continuous_const)).mul
      (continuous_snd.add continuous_const))
  · exact ((continuous_const.mul (continuous_angleClamp.comp continuous_fst)).mul
      continuous_const)

theorem continuous_angleParam (k j : ℕ) :
    Continuous fun q : ℝ × ℝ => angleParam k j q.1 q.2 :=
  (continuous_const.min (continuous_const.max (continuous_angleRaw k j))).sub continuous_const

/-- At time `0` the clamp is inactive on `(−π, π]` and the reparametrisation is the
identity. -/
theorem angleParam_param_zero (k j : ℕ) {φ : ℝ} (h1 : -Real.pi < φ) (h2 : φ ≤ Real.pi) :
    angleParam k j 0 φ = φ := by
  have hraw : angleRaw k j 0 φ = φ + Real.pi := by
    rw [angleRaw, angleClamp_zero]
    ring
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [angleParam, hraw, max_eq_right (by linarith), min_eq_right (by linarith)]
  ring

/-- **Saturation at the top**: the reparametrised angle is `π`, a point of the wall. -/
theorem angleParam_eq_pi_of_le {k j : ℕ} {θ φ : ℝ} (h : 2 * Real.pi ≤ angleRaw k j θ φ) :
    angleParam k j θ φ = Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [angleParam, max_eq_right (by linarith), min_eq_left h]
  ring

/-- **Saturation at the bottom**: the reparametrised angle is `−π`, the same point of the
wall. -/
theorem angleParam_eq_neg_pi_of_le {k j : ℕ} {θ φ : ℝ} (h : angleRaw k j θ φ ≤ 0) :
    angleParam k j θ φ = -Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [angleParam, max_eq_left h, min_eq_right (by linarith)]
  ring

/-- At the top end of the pinch interval every factor is saturated, for every `θ` and every
`j ≤ k`. -/
theorem angleParam_pi {k j : ℕ} (hjk : j ≤ k) (θ : ℝ) :
    angleParam k j θ Real.pi = Real.pi := by
  refine angleParam_eq_pi_of_le ?_
  have hc0 : 0 ≤ angleClamp θ := angleClamp_nonneg θ
  have hjk' : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpre : (0 : ℝ) ≤ 2 * Real.pi * angleClamp θ :=
    mul_nonneg (by linarith) hc0
  have hkey : 0 ≤ 2 * Real.pi * angleClamp θ * ((k : ℝ) - j) :=
    mul_nonneg hpre (by linarith)
  have hid : (1 + angleClamp θ * k) * (Real.pi + Real.pi)
      - 2 * Real.pi * angleClamp θ * j
      = 2 * Real.pi + 2 * Real.pi * angleClamp θ * ((k : ℝ) - j) := by ring
  rw [angleRaw, hid]
  linarith

/-- At the bottom end of the pinch interval every factor is saturated, for every `θ` and
every `j`. -/
theorem angleParam_neg_pi (k j : ℕ) (θ : ℝ) :
    angleParam k j θ (-Real.pi) = -Real.pi := by
  refine angleParam_eq_neg_pi_of_le ?_
  have hc0 : 0 ≤ angleClamp θ := angleClamp_nonneg θ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hraw : angleRaw k j θ (-Real.pi) = -(2 * Real.pi * angleClamp θ * j) := by
    rw [angleRaw]
    ring
  have hpre : (0 : ℝ) ≤ 2 * Real.pi * angleClamp θ :=
    mul_nonneg (by linarith) hc0
  have hnn : (0 : ℝ) ≤ 2 * Real.pi * angleClamp θ * (j : ℝ) :=
    mul_nonneg hpre (Nat.cast_nonneg j)
  rw [hraw]
  linarith

end AngleParam

/-! ## The scalar maps -/

section Scalar

theorem exp_pi_I : Complex.exp ((Real.pi : ℝ) * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

theorem exp_neg_pi_I : Complex.exp (((-Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
  have h : (((-Real.pi : ℝ) : ℂ)) * Complex.I = -(((Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **The wall map**: send `z` to the point of the non-positive real axis with the same
modulus. -/
def wallC (z : ℂ) : ℂ := -((‖z‖ : ℝ) : ℂ)

theorem norm_wallC (z : ℂ) : ‖wallC z‖ = ‖z‖ := by
  rw [wallC, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]

theorem continuous_wallC : Continuous wallC :=
  (Complex.continuous_ofReal.comp continuous_norm).neg

theorem wallC_smul {r : ℝ} (hr : 0 ≤ r) (z : ℂ) : wallC ((r : ℂ) * z) = (r : ℂ) * wallC z := by
  rw [wallC, wallC, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  push_cast
  ring

/-- **The angle reparametrisation, in the plane coordinate.** -/
def angleC (k j : ℕ) (θ : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ : ℝ) : ℂ) * Complex.exp (((angleParam k j θ (Complex.arg z) : ℝ) : ℂ) * Complex.I)

theorem norm_angleC (k j : ℕ) (θ : ℝ) (z : ℂ) : ‖angleC k j θ z‖ = ‖z‖ := by
  rw [angleC, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem angleC_zero (k j : ℕ) (θ : ℝ) : angleC k j θ 0 = 0 := by
  rw [angleC, norm_zero]
  simp

/-- At time `0` the reparametrisation is the identity. -/
theorem angleC_param_zero (k j : ℕ) (z : ℂ) : angleC k j 0 z = z := by
  rw [angleC, angleParam_param_zero k j (Complex.neg_pi_lt_arg z) (Complex.arg_le_pi z)]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- **Where the clamp saturates, the reparametrisation is the wall map.**  Both ends of the
pinch interval give the same point, which is the whole reason the angle coordinate works
where a suspension coordinate does not. -/
theorem angleC_eq_wallC {k j : ℕ} {θ : ℝ} {z : ℂ}
    (h : angleParam k j θ (Complex.arg z) = Real.pi ∨
      angleParam k j θ (Complex.arg z) = -Real.pi) : angleC k j θ z = wallC z := by
  rw [angleC, wallC]
  rcases h with h | h
  · rw [h, exp_pi_I]
    ring
  · rw [h, exp_neg_pi_I]
    ring

theorem angleC_smul {r : ℝ} (hr : 0 ≤ r) (k j : ℕ) (θ : ℝ) (z : ℂ) :
    angleC k j θ ((r : ℂ) * z) = (r : ℂ) * angleC k j θ z := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h]
    simp [angleC_zero]
  · rw [angleC, angleC, Complex.arg_real_mul z h, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr]
    push_cast
    ring

/-- **The limit of the clamped angle**, from the limits of its two arguments.  Stated for a
general filter so that it serves both the `ContinuousAt` use on the slit plane and the two
one-sided uses at the cut.  Built from one-variable combinators on purpose: composing the
two-variable `angleParam` with a pair-valued map sends `isDefEq` into a heartbeat
timeout. -/
theorem tendsto_angleParam {X : Type*} {l : Filter X} {u v : X → ℝ} {a b : ℝ}
    (hu : Filter.Tendsto u l (nhds a)) (hv : Filter.Tendsto v l (nhds b)) (k j : ℕ) :
    Filter.Tendsto (fun x => angleParam k j (u x) (v x)) l
      (nhds (angleParam k j a b)) := by
  have hcl : Filter.Tendsto (fun x => angleClamp (u x)) l (nhds (angleClamp a)) := by
    simpa only [Function.comp_def] using (continuous_angleClamp.tendsto a).comp hu
  have hraw : Filter.Tendsto (fun x => angleRaw k j (u x) (v x)) l
      (nhds (angleRaw k j a b)) := by
    simp only [angleRaw]
    exact ((tendsto_const_nhds.add (hcl.mul tendsto_const_nhds)).mul
      (hv.add tendsto_const_nhds)).sub ((tendsto_const_nhds.mul hcl).mul tendsto_const_nhds)
  simp only [angleParam]
  exact (tendsto_const_nhds.min (tendsto_const_nhds.max hraw)).sub tendsto_const_nhds

set_option maxHeartbeats 800000 in
/-- **Continuity, the cut included.**  Away from the non-positive reals this is
`Complex.continuousAt_arg`; at the origin it is the damping `‖angleC z‖ = ‖z‖`; and at a
negative real the two one-sided limits of `arg` are `π` and `−π`, at both of which the
clamp is saturated and `exp` takes the value `−1`. -/
theorem continuous_angleC (k j : ℕ) (hjk : j ≤ k) :
    Continuous fun p : ℝ × ℂ => angleC k j p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨θ₀, z₀⟩
  rcases eq_or_ne z₀ 0 with hz | hz
  · -- damped at the origin
    subst hz
    refine continuousAt_of_norm_le (r := fun p : ℝ × ℂ => ‖p.2‖)
      (fun p => le_of_eq (norm_angleC k j p.1 p.2)) ?_ (angleC_zero k j θ₀)
    have hn : Continuous fun p : ℝ × ℂ => ‖p.2‖ := continuous_snd.norm
    have h := hn.tendsto ((θ₀, (0 : ℂ)))
    simpa using h
  · by_cases hs : z₀ ∈ Complex.slitPlane
    · -- `arg` is continuous here
      have harg : ContinuousAt (fun p : ℝ × ℂ => Complex.arg p.2) (θ₀, z₀) :=
        (Complex.continuousAt_arg hs).comp' continuousAt_snd
      have hap : ContinuousAt
          (fun p : ℝ × ℂ => angleParam k j p.1 (Complex.arg p.2)) (θ₀, z₀) :=
        tendsto_angleParam continuousAt_fst harg k j
      have h1 : ContinuousAt (fun p : ℝ × ℂ => ((‖p.2‖ : ℝ) : ℂ)) (θ₀, z₀) :=
        (Complex.continuous_ofReal.comp' continuous_snd.norm).continuousAt
      have hof : ContinuousAt
          (fun p : ℝ × ℂ => ((angleParam k j p.1 (Complex.arg p.2) : ℝ) : ℂ)) (θ₀, z₀) :=
        Complex.continuous_ofReal.continuousAt.comp' hap
      have h2 : ContinuousAt (fun p : ℝ × ℂ =>
          Complex.exp (((angleParam k j p.1 (Complex.arg p.2) : ℝ) : ℂ) * Complex.I))
          (θ₀, z₀) :=
        Complex.continuous_exp.continuousAt.comp' (hof.mul continuousAt_const)
      exact h1.mul h2
    · -- `z₀` is a negative real
      have him : z₀.im = 0 := by
        by_contra hcon
        exact hs (Complex.mem_slitPlane_iff.2 (Or.inr hcon))
      have hre : z₀.re < 0 := by
        rcases lt_trichotomy z₀.re 0 with h | h | h
        · exact h
        · exact absurd (Complex.ext h him) hz
        · exact absurd (Complex.mem_slitPlane_iff.2 (Or.inl h)) hs
      have hargz : Complex.arg z₀ = Real.pi := Complex.arg_eq_pi_iff.2 ⟨hre, him⟩
      have hval : angleC k j θ₀ z₀ = wallC z₀ :=
        angleC_eq_wallC (Or.inl (by rw [hargz]; exact angleParam_pi hjk θ₀))
      -- split the neighbourhood into the two closed half planes
      have hsplit : (nhds ((θ₀, z₀) : ℝ × ℂ))
          = nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | 0 ≤ p.2.im} ⊔
            nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | p.2.im < 0} := by
        rw [← nhdsWithin_union]
        have huniv : ({p : ℝ × ℂ | 0 ≤ p.2.im} ∪ {p : ℝ × ℂ | p.2.im < 0}) = Set.univ := by
          ext p
          simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
          exact le_or_gt 0 p.2.im
        rw [huniv, nhdsWithin_univ]
      have hnormTend : ∀ S : Set (ℝ × ℂ), Filter.Tendsto
          (fun p : ℝ × ℂ => ((‖p.2‖ : ℝ) : ℂ))
          (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) S) (nhds ((‖z₀‖ : ℝ) : ℂ)) := by
        intro S
        have hcc : Continuous fun p : ℝ × ℂ => ((‖p.2‖ : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp' continuous_snd.norm
        exact (hcc.tendsto _).mono_left nhdsWithin_le_nhds
      have hfstTend : ∀ S : Set (ℝ × ℂ), Filter.Tendsto (fun p : ℝ × ℂ => p.1)
          (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) S) (nhds θ₀) :=
        fun S => (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
      show Filter.Tendsto (fun p : ℝ × ℂ => angleC k j p.1 p.2) (nhds ((θ₀, z₀) : ℝ × ℂ))
        (nhds (angleC k j θ₀ z₀))
      rw [hsplit, Filter.tendsto_sup]
      constructor
      · -- from the closed upper half plane, `arg → π`
        have hsub : Filter.Tendsto (fun p : ℝ × ℂ => p.2)
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | 0 ≤ p.2.im})
            (nhdsWithin z₀ {z : ℂ | 0 ≤ z.im}) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            ((continuous_snd.tendsto _).mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin
        have hargU : Filter.Tendsto (fun p : ℝ × ℂ => Complex.arg p.2)
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | 0 ≤ p.2.im}) (nhds Real.pi) := by
          have h := (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp
            hsub
          simpa only [Function.comp_def] using h
        have hapU : Filter.Tendsto
            (fun p : ℝ × ℂ => angleParam k j p.1 (Complex.arg p.2))
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | 0 ≤ p.2.im}) (nhds Real.pi) := by
          have h := tendsto_angleParam (hfstTend {p : ℝ × ℂ | 0 ≤ p.2.im}) hargU k j
          rwa [angleParam_pi hjk θ₀] at h
        have hexpU : Filter.Tendsto (fun p : ℝ × ℂ =>
            Complex.exp (((angleParam k j p.1 (Complex.arg p.2) : ℝ) : ℂ) * Complex.I))
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | 0 ≤ p.2.im}) (nhds (-1)) := by
          have hofU : Filter.Tendsto
              (fun p : ℝ × ℂ => ((angleParam k j p.1 (Complex.arg p.2) : ℝ) : ℂ) * Complex.I)
              (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | 0 ≤ p.2.im})
              (nhds (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
            have h := ((Complex.continuous_ofReal.tendsto Real.pi).comp hapU).mul
              (tendsto_const_nhds (x := Complex.I))
            simpa only [Function.comp_def] using h
          have h := (Complex.continuous_exp.tendsto (((Real.pi : ℝ) : ℂ) * Complex.I)).comp hofU
          rw [exp_pi_I] at h
          simpa only [Function.comp_def] using h
        have := (hnormTend {p : ℝ × ℂ | 0 ≤ p.2.im}).mul hexpU
        rw [hval, wallC]
        simpa only [angleC, mul_neg, mul_one] using this
      · -- from the open lower half plane, `arg → −π`
        have hsub : Filter.Tendsto (fun p : ℝ × ℂ => p.2)
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | p.2.im < 0})
            (nhdsWithin z₀ {z : ℂ | z.im < 0}) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            ((continuous_snd.tendsto _).mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin
        have hargL : Filter.Tendsto (fun p : ℝ × ℂ => Complex.arg p.2)
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | p.2.im < 0}) (nhds (-Real.pi)) := by
          have h := (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp hsub
          simpa only [Function.comp_def] using h
        have hapL : Filter.Tendsto
            (fun p : ℝ × ℂ => angleParam k j p.1 (Complex.arg p.2))
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | p.2.im < 0}) (nhds (-Real.pi)) := by
          have h := tendsto_angleParam (hfstTend {p : ℝ × ℂ | p.2.im < 0}) hargL k j
          rwa [angleParam_neg_pi k j θ₀] at h
        have hexpL : Filter.Tendsto (fun p : ℝ × ℂ =>
            Complex.exp (((angleParam k j p.1 (Complex.arg p.2) : ℝ) : ℂ) * Complex.I))
            (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | p.2.im < 0}) (nhds (-1)) := by
          have hofL : Filter.Tendsto
              (fun p : ℝ × ℂ => ((angleParam k j p.1 (Complex.arg p.2) : ℝ) : ℂ) * Complex.I)
              (nhdsWithin ((θ₀, z₀) : ℝ × ℂ) {p : ℝ × ℂ | p.2.im < 0})
              (nhds (((-Real.pi : ℝ) : ℂ) * Complex.I)) := by
            have h := ((Complex.continuous_ofReal.tendsto (-Real.pi)).comp hapL).mul
              (tendsto_const_nhds (x := Complex.I))
            simpa only [Function.comp_def] using h
          have h := (Complex.continuous_exp.tendsto (((-Real.pi : ℝ) : ℂ) * Complex.I)).comp hofL
          rw [exp_neg_pi_I] at h
          simpa only [Function.comp_def] using h
        have := (hnormTend {p : ℝ × ℂ | p.2.im < 0}).mul hexpL
        rw [hval, wallC]
        simpa only [angleC, mul_neg, mul_one] using this

end Scalar

/-! ## The family on `E` -/

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e₁ e₂ : E}

/-- **The wall retraction**: `(z, v) ↦ (−|z|, v)`.  Radial, so it maps the closed ball to
itself and the sphere to the sphere. -/
def wallRetract (e₁ e₂ : E) : E → E := planeSub e₁ e₂ wallC

theorem isRadialMap_wallRetract (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) : IsRadialMap (wallRetract e₁ e₂) :=
  isRadialMap_planeSub h₁ h₂ h₁₂ continuous_wallC norm_wallC
    (fun _ hr _ => wallC_smul hr _)

/-- **The `j`-th angle reparametrisation on `E`**, one of `k + 1`. -/
def angleRepar (e₁ e₂ : E) (k j : ℕ) (θ : ℝ) : E → E := planeSub e₁ e₂ (angleC k j θ)

theorem isRadialMap_angleRepar (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (k j : ℕ) (hjk : j ≤ k) (θ : ℝ) :
    IsRadialMap (angleRepar e₁ e₂ k j θ) :=
  isRadialMap_planeSub h₁ h₂ h₁₂
    ((continuous_angleC k j hjk).comp (continuous_const.prodMk continuous_id))
    (norm_angleC k j θ) (fun _ hr _ => angleC_smul hr k j θ _)

/-- At time `0` the family is the identity. -/
theorem angleRepar_param_zero (e₁ e₂ : E) (k j : ℕ) (y : E) :
    angleRepar e₁ e₂ k j 0 y = y := by
  rw [angleRepar, planeSub]
  simp only [angleC_param_zero]
  exact planeRest_add_planeC e₁ e₂ y

/-- **Joint continuity in `(θ, y)`**, which is what `reparProd` consumes. -/
theorem continuous_angleRepar (e₁ e₂ : E) (k j : ℕ) (hjk : j ≤ k) :
    Continuous fun p : ℝ × E => angleRepar e₁ e₂ k j p.1 p.2 := by
  have hrest : Continuous fun p : ℝ × E => planeRest e₁ e₂ p.2 :=
    (continuous_id.sub ((continuous_planeE e₁ e₂).comp (continuous_planeC e₁ e₂))).comp
      continuous_snd
  have hplane : Continuous fun p : ℝ × E => angleC k j p.1 (planeC e₁ e₂ p.2) :=
    (continuous_angleC k j hjk).comp
      (continuous_fst.prodMk ((continuous_planeC e₁ e₂).comp continuous_snd))
  exact hrest.add ((continuous_planeE e₁ e₂).comp hplane)

/-- The family preserves the closed ball, because it preserves the norm. -/
theorem norm_angleRepar (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (k j : ℕ) (θ : ℝ) (y : E) : ‖angleRepar e₁ e₂ k j θ y‖ = ‖y‖ :=
  norm_planeSub h₁ h₂ h₁₂ (norm_angleC k j θ) y

/-- **The reparametrisation family, indexed by all of `ℕ`.**  `reparProd` asks for
continuity at *every* index, but `angleRepar e₁ e₂ k j` is continuous only for `j ≤ k`:
past `k` the top end of the clamp stops saturating at intermediate `θ` and the map jumps
across the cut.  Clamping the index costs nothing, because the ordered product of `k + 1`
factors never reaches an index above `k`. -/
def angleFam (e₁ e₂ : E) (k j : ℕ) (θ : ℝ) : E → E := angleRepar e₁ e₂ k (min j k) θ

theorem angleFam_of_le (e₁ e₂ : E) {k j : ℕ} (hjk : j ≤ k) (θ : ℝ) :
    angleFam e₁ e₂ k j θ = angleRepar e₁ e₂ k j θ := by
  rw [angleFam, min_eq_left hjk]

theorem continuous_angleFam (e₁ e₂ : E) (k j : ℕ) :
    Continuous fun p : ℝ × E => angleFam e₁ e₂ k j p.1 p.2 :=
  continuous_angleRepar e₁ e₂ k (min j k) (min_le_right j k)

theorem angleFam_param_zero (e₁ e₂ : E) (k j : ℕ) (y : E) :
    angleFam e₁ e₂ k j 0 y = y :=
  angleRepar_param_zero e₁ e₂ k (min j k) y

theorem norm_angleFam (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ))
    (k j : ℕ) (θ : ℝ) (y : E) : ‖angleFam e₁ e₂ k j θ y‖ = ‖y‖ :=
  norm_angleRepar h₁ h₂ h₁₂ k (min j k) θ y

/-- **Off its own slab, the `j`-th factor is the wall retraction.**  This is the lemma the
pinch identification consumes: it says the other `k` factors of the ordered product
evaluate the clutching function at one and the same wall point. -/
theorem angleRepar_eq_wallRetract (e₁ e₂ : E) {k j : ℕ} {θ : ℝ} {y : E}
    (h : angleParam k j θ (Complex.arg (planeC e₁ e₂ y)) = Real.pi ∨
      angleParam k j θ (Complex.arg (planeC e₁ e₂ y)) = -Real.pi) :
    angleRepar e₁ e₂ k j θ y = wallRetract e₁ e₂ y := by
  rw [angleRepar, wallRetract, planeSub, planeSub, angleC_eq_wallC h]

end Family

/-! ## Collapsing an ordered product to a single factor -/

section Single

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]
  {W : E → Matrix n n ℂ} {P : ℕ → ℝ → E → E}

/-- **An ordered product all of whose factors are the identity matrix is the identity.** -/
theorem reparProd_eq_one {θ : ℝ} {y : E} :
    ∀ {m : ℕ}, (∀ j, j < m → W (P j θ y) = 1) → reparProd W P θ y m = 1
  | 0, _ => reparProd_zero W P θ y
  | (m + 1), h => by
      rw [reparProd_succ, h m (Nat.lt_succ_self m), Matrix.mul_one]
      exact reparProd_eq_one (fun j hj => h j (Nat.lt_succ_of_lt hj))

/-- Two reparametrisation families agreeing below `m` give the same ordered product. -/
theorem reparProd_congr {θ : ℝ} {y : E} {P P' : ℕ → ℝ → E → E} :
    ∀ {m : ℕ}, (∀ j, j < m → P j θ y = P' j θ y) →
      reparProd W P θ y m = reparProd W P' θ y m
  | 0, _ => by rw [reparProd_zero, reparProd_zero]
  | (m + 1), h => by
      rw [reparProd_succ, reparProd_succ, h m (Nat.lt_succ_self m),
        reparProd_congr (fun j hj => h j (Nat.lt_succ_of_lt hj))]

/-- **An ordered product all of whose factors but one are the identity matrix collapses to
that factor.**  This is the shape the pinch identification produces: at time `1` every
factor but the one owning the point's slab evaluates `W` at the same wall point, where `W`
is `1`. -/
theorem reparProd_eq_single {θ : ℝ} {y : E} :
    ∀ {m i : ℕ}, i < m → (∀ j, j < m → j ≠ i → W (P j θ y) = 1) →
      reparProd W P θ y m = W (P i θ y)
  | 0, i, him, _ => absurd him (Nat.not_lt_zero i)
  | (m + 1), i, him, h1 => by
      rw [reparProd_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp him with h | h
      · have hne : m ≠ i := Nat.ne_of_gt h
        rw [h1 m (Nat.lt_succ_self m) hne, Matrix.mul_one]
        exact reparProd_eq_single h (fun j hj hji => h1 j (Nat.lt_succ_of_lt hj) hji)
      · subst h
        rw [reparProd_eq_one (fun j hj => h1 j (Nat.lt_succ_of_lt hj) (Nat.ne_of_lt hj)),
          Matrix.one_mul]

end Single

end

end Powers
end LIX
end GroupApproximation
