import GroupApproximation.Analysis.LIXLemmaSixFrameGeneric
import GroupApproximation.Meta.AxiomGuard

/-!
# The unitary field of Corollary 4 at rank `n`, gauged and pulled back

`Analysis/LIXLemmaSixField.lean` builds, at rank two, a continuous unitary field over `S⁵ × Y`
conjugating the constant complement `bigE` onto the moving one `bigF`, out of a null-homotopy of
the stage unitary `u ⊕ c`.  This file is that construction at every rank `n`, with two extra
parameters, and the `k`-indexed Corollary 4 needs both.

* **A gauge `g`.**  The endpoint witness of the stronger theorem is the renormalised generator
  `ũ = Aᴴ u` (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3).  Its seam is not `u` but `ũ`, and
  the field accounts for that by gauging the northern frame: `frameNorth (ξ x) · (g x ⊕ 1)`.  A
  gauge that is continuous and unitary on the whole sphere is all that is asked; lane
  `lix-powers`' ball extension of the wall part supplies one.
* **A pullback `ξ`.**  For the `k`-th power the seam is `ũ ∘ ψ`, and the frames are read at
  `Σψ x` rather than at `x`.  `ξ` is any continuous self-map of `S^{2n+1}` that fixes the
  clutching coordinate, so it preserves both caps; the conclusion conjugates onto `bigF (ξ x)`.

The seam hypothesis is stated **pointwise on the equator**, at the cone direction `dirPt x`:

    W 1 (dirPt x) y = (g x)ᴴ · genU2 (ξ x)  ⊕  c y .

So nothing about `ψ`, `ũ` or the radial maps enters the geometry of this file.  With `ξ = id` and
`g = 1` it is the rank-`n` form of `exists_unitary_field_of_nullHomotopy`.

## Why there is still no analysis at the pole

As at rank two, the cone time `capTime x = max 0 (1 + 2 Re x_last)` is clamped, so on the collar
`{Re x_last ≤ -1/2}` the correction is the constant `W 0 = 1` whatever the direction is.

## Main results

* `Gen.equatorInv`, `Gen.equatorEmb_equatorInv`, `Gen.norm_sq_equatorInv` — the equator chart.
* `Gen.capTime`, `Gen.dirPt` — the cone coordinates.
* `Gen.extTop` — `g ⊕ 1` on `ℂ^{n+1} = pole^⊥ ⊕ ℂ·pole`, with `extTop_genU2 : extTop (genU2 x) = genU x`.
* `Gen.southAtG_eq_northFG` — **the gauged seam**.
* `Gen.exists_unitary_field_of_nullHomotopy_gauged` — **the analytic half of Corollary 4 at rank
  `n`, gauged and pulled back**.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

open scoped Matrix ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The caps of `S^{2n+1}` -/

section Caps

variable {n : ℕ}

/-- The clutching coordinate `Re x_last` of a point of `S^{2n+1}`. -/
def capHeight (n : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) : ℝ :=
  ((x : Fin (n + 1) → ℂ) (Fin.last n)).re

theorem continuous_capHeight (n : ℕ) : Continuous (capHeight n) :=
  Complex.continuous_re.comp ((continuous_apply (Fin.last n)).comp continuous_subtype_val)

theorem ne_neg_one_of_nonneg_re {z : ℂ} (h : 0 ≤ z.re) : z ≠ -1 := by
  intro hc
  rw [hc] at h
  norm_num at h

theorem ne_one_of_nonpos_re {z : ℂ} (h : z.re ≤ 0) : z ≠ 1 := by
  intro hc
  rw [hc] at h
  norm_num at h

/-- A self-map of `S^{2n+1}` fixing the clutching coordinate: it preserves both caps. -/
structure IsCapDatum (n : ℕ) (ξ : ↥(STW59.Gen.sphereOdd n) → Fin (n + 1) → ℂ) : Prop where
  continuous : Continuous ξ
  mem : ∀ x, ξ x ∈ STW59.unitVectors (Fin (n + 1))
  last : ∀ x, ξ x (Fin.last n) = (x : Fin (n + 1) → ℂ) (Fin.last n)

/-- The identity is a cap datum. -/
theorem isCapDatum_id (n : ℕ) : IsCapDatum n fun x => (x : Fin (n + 1) → ℂ) where
  continuous := continuous_subtype_val
  mem x := x.2
  last _ := rfl

end Caps

/-! ## 2. The equator chart -/

section EquatorChart

variable {n : ℕ}

/-- The real coordinates of a point of `ℂ^{n+1}`, indexed as `n` complex pairs plus the imaginary
part of the clutching coordinate: the order `Gen.equatorEmb n` reads them in. -/
def eqCoord (n : ℕ) (x : Fin (n + 1) → ℂ) : (Fin n × Fin 2) ⊕ Unit → ℝ
  | Sum.inl (i, b) => if (b : ℕ) = 0 then (x i.castSucc).re else (x i.castSucc).im
  | Sum.inr _ => (x (Fin.last n)).im

/-- **The inverse of `Gen.equatorEmb n` on the equator**, with no normalisation: it forgets the
real part of the clutching coordinate. -/
def equatorInv (n : ℕ) (x : Fin (n + 1) → ℂ) : EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  WithLp.toLp 2 fun k => eqCoord n x (eqBwd n k)

theorem equatorInv_eqFwd (n : ℕ) (x : Fin (n + 1) → ℂ) (s : (Fin n × Fin 2) ⊕ Unit) :
    equatorInv n x (eqFwd n s) = eqCoord n x s := by
  show eqCoord n x (eqBwd n (eqFwd n s)) = eqCoord n x s
  rw [eqBwd_eqFwd]

/-- **The round trip on the equator.** -/
theorem equatorEmb_equatorInv (n : ℕ) {x : Fin (n + 1) → ℂ} (h : (x (Fin.last n)).re = 0) :
    equatorEmb n (equatorInv n x) = x := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [equatorEmb_last, equatorInv_eqFwd]
    apply Complex.ext <;> simp [eqCoord, h]
  · rw [equatorEmb_castSucc, equatorInv_eqFwd, equatorInv_eqFwd]
    apply Complex.ext <;> simp [eqCoord]

/-- The chart forgets exactly `(Re x_last)²` of the norm. -/
theorem norm_sq_equatorInv (n : ℕ) (x : Fin (n + 1) → ℂ) :
    ‖equatorInv n x‖ ^ 2 = (∑ i, ‖x i‖ ^ 2) - ((x (Fin.last n)).re) ^ 2 := by
  classical
  have hre : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hR : ‖equatorInv n x‖ ^ 2 = ∑ k : Fin (2 * n + 1), ‖equatorInv n x k‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  have hE : ∑ k : Fin (2 * n + 1), ‖equatorInv n x k‖ ^ 2
      = ∑ s : (Fin n × Fin 2) ⊕ Unit, ‖equatorInv n x (eqFwd n s)‖ ^ 2 :=
    (Fintype.sum_equiv (eqIdx n) (fun s => ‖equatorInv n x (eqFwd n s)‖ ^ 2)
      (fun k => ‖equatorInv n x k‖ ^ 2) (fun s => by rw [eqIdx_apply])).symm
  have hS : ∑ s : (Fin n × Fin 2) ⊕ Unit, ‖equatorInv n x (eqFwd n s)‖ ^ 2
      = (∑ i : Fin n, ((x i.castSucc).re ^ 2 + (x i.castSucc).im ^ 2))
        + (x (Fin.last n)).im ^ 2 := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) ?_
    · rw [Fin.sum_univ_two, equatorInv_eqFwd, equatorInv_eqFwd]
      simp [eqCoord, Real.norm_eq_abs, sq_abs]
    · simp [equatorInv_eqFwd, eqCoord, Real.norm_eq_abs, sq_abs]
  have hX : ∑ i, ‖x i‖ ^ 2
      = (∑ i : Fin n, ((x i.castSucc).re ^ 2 + (x i.castSucc).im ^ 2))
        + ((x (Fin.last n)).re ^ 2 + (x (Fin.last n)).im ^ 2) := by
    rw [Fin.sum_univ_castSucc]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => hre _) (hre _)
  rw [hR, hE, hS, hX]
  ring

theorem continuous_equatorInv (n : ℕ) : Continuous (equatorInv n) := by
  have hs : ∀ s : (Fin n × Fin 2) ⊕ Unit,
      Continuous fun x : Fin (n + 1) → ℂ => eqCoord n x s := by
    rintro (⟨i, b⟩ | u)
    · by_cases hb : (b : ℕ) = 0
      · simp only [eqCoord, if_pos hb]
        exact Complex.continuous_re.comp (continuous_apply _)
      · simp only [eqCoord, if_neg hb]
        exact Complex.continuous_im.comp (continuous_apply _)
    · simp only [eqCoord]
      exact Complex.continuous_im.comp (continuous_apply _)
  exact (PiLp.continuous_toLp 2 fun _ : Fin (2 * n + 1) => ℝ).comp
    (continuous_pi fun k => hs (eqBwd n k))

theorem equatorInv_ne_zero {x : Fin (n + 1) → ℂ} (hx : x ∈ STW59.unitVectors (Fin (n + 1)))
    (h : (x (Fin.last n)).re ^ 2 < 1) : equatorInv n x ≠ 0 := by
  have hsum : (∑ i, ‖x i‖ ^ 2 : ℝ) = 1 := hx
  intro hc
  have h2 := norm_sq_equatorInv n x
  rw [hc, norm_zero, hsum] at h2
  nlinarith

end EquatorChart

/-! ## 3. The cone coordinates of the southern cap -/

section Cone

variable {n : ℕ}

/-- The clamped cone time: `1` on the equator, `0` on the collar `{Re x_last ≤ -1/2}`. -/
def capTime (n : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) : ℝ := max 0 (1 + 2 * capHeight n x)

theorem continuous_capTime (n : ℕ) : Continuous (capTime n) :=
  continuous_const.max (continuous_const.add (continuous_const.mul (continuous_capHeight n)))

theorem capTime_eq_one {x : ↥(STW59.Gen.sphereOdd n)} (h : capHeight n x = 0) :
    capTime n x = 1 := by
  simp only [capTime, h]
  norm_num

theorem capTime_eq_zero {x : ↥(STW59.Gen.sphereOdd n)} (h : capHeight n x ≤ -(1 / 2)) :
    capTime n x = 0 := by
  simp only [capTime]
  exact max_eq_left (by linarith)

open scoped Classical in
/-- The equatorial direction of a point of `S^{2n+1}`, away from the two poles. -/
def dirPt (n : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) : ↥(STW59.Gen.sphereEven n) :=
  if h : equatorInv n (x : Fin (n + 1) → ℂ) = 0 then Classical.arbitrary _
  else ⟨‖equatorInv n (x : Fin (n + 1) → ℂ)‖⁻¹ • equatorInv n (x : Fin (n + 1) → ℂ),
    mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm h)⟩

theorem coe_dirPt_of_ne {x : ↥(STW59.Gen.sphereOdd n)}
    (h : equatorInv n (x : Fin (n + 1) → ℂ) ≠ 0) :
    (dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1)))
      = ‖equatorInv n (x : Fin (n + 1) → ℂ)‖⁻¹ • equatorInv n (x : Fin (n + 1) → ℂ) := by
  simp only [dirPt, dif_neg h]

theorem continuousAt_dirPt {x₀ : ↥(STW59.Gen.sphereOdd n)}
    (h : equatorInv n (x₀ : Fin (n + 1) → ℂ) ≠ 0) : ContinuousAt (dirPt n) x₀ := by
  refine continuousAt_subtype_mk ?_
  have hc : Continuous fun x : ↥(STW59.Gen.sphereOdd n) => equatorInv n (x : Fin (n + 1) → ℂ) :=
    (continuous_equatorInv n).comp continuous_subtype_val
  have hopen : IsOpen {x : ↥(STW59.Gen.sphereOdd n) | equatorInv n (x : Fin (n + 1) → ℂ) ≠ 0} :=
    isOpen_ne.preimage hc
  have heq : (fun x : ↥(STW59.Gen.sphereOdd n) =>
        ((dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1)))))
      =ᶠ[nhds x₀] fun x : ↥(STW59.Gen.sphereOdd n) =>
        ‖equatorInv n (x : Fin (n + 1) → ℂ)‖⁻¹ • equatorInv n (x : Fin (n + 1) → ℂ) :=
    Filter.eventually_of_mem (hopen.mem_nhds h) fun x hx => coe_dirPt_of_ne hx
  refine ContinuousAt.congr ?_ heq.symm
  exact ContinuousAt.smul (ContinuousAt.inv₀ hc.norm.continuousAt (norm_ne_zero_iff.mpr h))
    hc.continuousAt

/-- **On the equator the cone direction embeds back to the point.** -/
theorem equatorEmb_dirPt {x : ↥(STW59.Gen.sphereOdd n)} (h : capHeight n x = 0) :
    equatorEmb n ((dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1)))) = (x : Fin (n + 1) → ℂ) := by
  have hsum : (∑ i, ‖(x : Fin (n + 1) → ℂ) i‖ ^ 2 : ℝ) = 1 := x.2
  have hre : ((x : Fin (n + 1) → ℂ) (Fin.last n)).re = 0 := h
  have hn : ‖equatorInv n (x : Fin (n + 1) → ℂ)‖ ^ 2 = 1 := by
    rw [norm_sq_equatorInv, hsum, hre]
    ring
  have hn1 : ‖equatorInv n (x : Fin (n + 1) → ℂ)‖ = 1 := by
    nlinarith [norm_nonneg (equatorInv n (x : Fin (n + 1) → ℂ))]
  have hne : equatorInv n (x : Fin (n + 1) → ℂ) ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hn1
    exact zero_ne_one hn1
  rw [coe_dirPt_of_ne hne, hn1, inv_one, one_smul, equatorEmb_equatorInv n hre]

end Cone

/-! ## 4. The frames along a pullback -/

section Frames

variable {n : ℕ}

theorem continuousOn_frameNorth_comp {Z : Type*} [TopologicalSpace Z] {ξ : Z → Fin (n + 1) → ℂ}
    (hξ : Continuous ξ) (hmem : ∀ z, ξ z ∈ STW59.unitVectors (Fin (n + 1))) :
    ContinuousOn (fun z => frameNorth (ePole n) (ξ z)) {z | ξ z (Fin.last n) ≠ -1} := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_frameRot continuous_const (hξ.comp continuous_subtype_val)
    (fun s => isFrameDatum_ePole (hmem s.1) s.2)

theorem continuousOn_frameSouth_comp {Z : Type*} [TopologicalSpace Z] {ξ : Z → Fin (n + 1) → ℂ}
    (hξ : Continuous ξ) (hmem : ∀ z, ξ z ∈ STW59.unitVectors (Fin (n + 1))) :
    ContinuousOn (fun z => frameSouth (ePole n) (ξ z)) {z | ξ z (Fin.last n) ≠ 1} := by
  rw [continuousOn_iff_continuous_restrict]
  exact (continuous_frameRot continuous_const (hξ.comp continuous_subtype_val)
    (fun s => isFrameDatum_neg_ePole (hmem s.1) s.2)).mul continuous_const

/-- The southern frame corrected by the generator is the northern frame. -/
theorem frameSouth_mul_genU_conjTranspose {x : Fin (n + 1) → ℂ}
    (hx : x ∈ STW59.unitVectors (Fin (n + 1))) (hS : x (Fin.last n) ≠ 1) :
    frameSouth (ePole n) x * (genU n x)ᴴ = frameNorth (ePole n) x := by
  have h1 : (genU n x)ᴴ = (frameSouth (ePole n) x)ᴴ * frameNorth (ePole n) x := by
    rw [genU, seamGen, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [h1, ← Matrix.mul_assoc,
    frameSouth_mul_conjTranspose (unit_ePole n) (isFrameDatum_neg_ePole hx hS), Matrix.one_mul]

end Frames

/-! ## 5. The gauge `g ⊕ 1` -/

section Gauge

variable {n : ℕ}

/-- `g ⊕ 1` on `ℂ^{n+1} = pole^⊥ ⊕ ℂ·pole`. -/
def extTop (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  incl n * g * (incl n)ᴴ + rk1 (ePole n) (ePole n)

theorem conjTranspose_incl_mul_rk1 (n : ℕ) :
    (incl n)ᴴ * rk1 (ePole n) (ePole n) = 0 := by
  calc (incl n)ᴴ * rk1 (ePole n) (ePole n) = (incl n)ᴴ * (1 - incl n * (incl n)ᴴ) := by
        rw [incl_mul_conjTranspose, sub_sub_cancel]
    _ = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, incl_conjTranspose_mul,
          Matrix.one_mul, sub_self]

theorem rk1_mul_incl (n : ℕ) : rk1 (ePole n) (ePole n) * incl n = 0 := by
  have h := congrArg Matrix.conjTranspose (conjTranspose_incl_mul_rk1 n)
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, rk1_conjTranspose,
    Matrix.conjTranspose_zero] at h

theorem incl_conj_mul_rk1 (g : Matrix (Fin n) (Fin n) ℂ) :
    incl n * g * (incl n)ᴴ * rk1 (ePole n) (ePole n) = 0 := by
  simp only [Matrix.mul_assoc]
  rw [conjTranspose_incl_mul_rk1, Matrix.mul_zero, Matrix.mul_zero]

theorem rk1_mul_incl_conj (g : Matrix (Fin n) (Fin n) ℂ) :
    rk1 (ePole n) (ePole n) * (incl n * g * (incl n)ᴴ) = 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rk1_mul_incl, Matrix.zero_mul, Matrix.zero_mul]

theorem extTop_mul (g h : Matrix (Fin n) (Fin n) ℂ) :
    extTop n (g * h) = extTop n g * extTop n h := by
  have e1 : incl n * g * (incl n)ᴴ * (incl n * h * (incl n)ᴴ)
      = incl n * (g * h) * (incl n)ᴴ := by
    calc incl n * g * (incl n)ᴴ * (incl n * h * (incl n)ᴴ)
        = incl n * (g * (((incl n)ᴴ * incl n) * (h * (incl n)ᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = incl n * (g * h) * (incl n)ᴴ := by
          rw [incl_conjTranspose_mul, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
  rw [extTop, extTop, extTop, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1,
    incl_conj_mul_rk1, rk1_mul_incl_conj, rk1_ePole_mul_self]
  abel

theorem extTop_conjTranspose (g : Matrix (Fin n) (Fin n) ℂ) : (extTop n g)ᴴ = extTop n gᴴ := by
  rw [extTop, extTop, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, rk1_conjTranspose]
  simp only [Matrix.mul_assoc]

theorem extTop_one : extTop n (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [extTop, Matrix.mul_one, incl_mul_conjTranspose, sub_add_cancel]

theorem extTop_conjTranspose_mul_self {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) :
    (extTop n g)ᴴ * extTop n g = 1 := by
  rw [extTop_conjTranspose, ← extTop_mul, hg, extTop_one]

theorem extTop_mul_conjTranspose {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * gᴴ = 1) :
    extTop n g * (extTop n g)ᴴ = 1 := by
  rw [extTop_conjTranspose, ← extTop_mul, hg, extTop_one]

theorem extTop_mul_rk1 (g : Matrix (Fin n) (Fin n) ℂ) :
    extTop n g * rk1 (ePole n) (ePole n) = rk1 (ePole n) (ePole n) := by
  rw [extTop, Matrix.add_mul, incl_conj_mul_rk1, rk1_ePole_mul_self, zero_add]

theorem rk1_mul_extTop (g : Matrix (Fin n) (Fin n) ℂ) :
    rk1 (ePole n) (ePole n) * extTop n g = rk1 (ePole n) (ePole n) := by
  rw [extTop, Matrix.mul_add, rk1_mul_incl_conj, rk1_ePole_mul_self, zero_add]

/-- The gauge fixes the pole, so it does not move the constant complement. -/
theorem extTop_conj_compl {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * gᴴ = 1) :
    extTop n g * (1 - rk1 (ePole n) (ePole n)) * (extTop n g)ᴴ = 1 - rk1 (ePole n) (ePole n) := by
  have hcomm : extTop n g * (1 - rk1 (ePole n) (ePole n))
      = (1 - rk1 (ePole n) (ePole n)) * extTop n g := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, extTop_mul_rk1,
      rk1_mul_extTop]
  rw [hcomm, Matrix.mul_assoc, extTop_mul_conjTranspose hg, Matrix.mul_one]

/-- **The compression of the generator, filled back in**: `genU2 x ⊕ 1 = genU x`. -/
theorem extTop_genU2 {x : Fin (n + 1) → ℂ} (hx : x ∈ STW59.unitVectors (Fin (n + 1)))
    (hN : x (Fin.last n) ≠ -1) (hS : x (Fin.last n) ≠ 1) :
    extTop n (genU2 n x) = genU n x := by
  have h1 : incl n * genU2 n x * (incl n)ᴴ
      = incl n * (incl n)ᴴ * genU n x * (incl n * (incl n)ᴴ) := by
    rw [genU2]
    simp only [Matrix.mul_assoc]
  rw [extTop, h1, incl_mul_conjTranspose]
  have h2 : (1 - rk1 (ePole n) (ePole n)) * genU n x * (1 - rk1 (ePole n) (ePole n))
      = (1 - rk1 (ePole n) (ePole n)) * ((1 - rk1 (ePole n) (ePole n)) * genU n x) := by
    rw [Matrix.mul_assoc, ← genU_comm_compl hx hN hS]
  rw [h2, ← Matrix.mul_assoc, one_sub_mul_one_sub (rk1_ePole_mul_self n), Matrix.sub_mul,
    Matrix.one_mul, rk1_ePole_mul_genU hx hN hS]
  abel

theorem continuous_extTop : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => extTop n g :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).add continuous_const

end Gauge

/-! ## 6. The two blocks under the extension -/

section Blocks

variable {n : ℕ} {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y] {P : Y → Matrix HI HI ℂ} {y : Y}

theorem extAmb_topBlock (S : Matrix (Fin n) (Fin n) ℂ) :
    extAmb n P y (Matrix.fromBlocks S 0 0 (P y)) = frameAmb n HI (extTop n S) := by
  have h1 : P y + (1 - P y) = (1 : Matrix HI HI ℂ) := by abel
  rw [extAmb_fromBlocks, h1, frameAmb, extTop]

theorem extAmb_coBlock (D : Matrix HI HI ℂ) :
    extAmb n P y (Matrix.fromBlocks 1 0 0 D) = coframeAmb n HI (D + (1 - P y)) := by
  have h1 : incl n * (1 : Matrix (Fin n) (Fin n) ℂ) * (incl n)ᴴ + rk1 (ePole n) (ePole n)
      = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    rw [Matrix.mul_one, incl_mul_conjTranspose]
    abel
  rw [extAmb_fromBlocks, h1, coframeAmb]

theorem isCornerUnit_coBlock {D : Matrix HI HI ℂ} (hc1 : Dᴴ * D = P y) (hc2 : D * Dᴴ = P y) :
    IsCornerUnit n P y (Matrix.fromBlocks 1 0 0 D) where
  star_mul := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, hc1, cornerE]
  mul_star := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, hc2, cornerE]

theorem isCornerUnit_topBlock {S : Matrix (Fin n) (Fin n) ℂ} (hS1 : Sᴴ * S = 1)
    (hS2 : S * Sᴴ = 1) (hP : P y * P y = P y) (hPs : (P y)ᴴ = P y) :
    IsCornerUnit n P y (Matrix.fromBlocks S 0 0 (P y)) where
  star_mul := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, hS1, hPs, hP, cornerE]
  mul_star := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, hS2, hPs, hP, cornerE]

end Blocks

/-! ## 7. The two hemisphere fields, gauged and pulled back -/

section Fields

variable {n : ℕ} {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y]

/-- The northern field: the northern frame at `ξ x`, gauged by `g x ⊕ 1`, padded by `𝟏_H`. -/
def northFG (n : ℕ) (HI : Type*) [Fintype HI] [DecidableEq HI]
    (ξ : ↥(STW59.Gen.sphereOdd n) → Fin (n + 1) → ℂ)
    (g : ↥(STW59.Gen.sphereOdd n) → Matrix (Fin n) (Fin n) ℂ) (x : ↥(STW59.Gen.sphereOdd n)) :
    Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ :=
  frameAmb n HI (frameNorth (ePole n) (ξ x) * extTop n (g x))

/-- The southern field at a point of `S^{2n+1}` and a point of `Y`. -/
def southAtG (n : ℕ) (P c : Y → Matrix HI HI ℂ)
    (W : ℝ → ↥(STW59.Gen.sphereEven n) → Y → Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ)
    (ξ : ↥(STW59.Gen.sphereOdd n) → Fin (n + 1) → ℂ) (x : ↥(STW59.Gen.sphereOdd n)) (y : Y) :
    Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ :=
  frameAmb n HI (frameSouth (ePole n) (ξ x)) * (extAmb n P y (W (capTime n x) (dirPt n x) y))ᴴ
    * extAmb n P y (Matrix.fromBlocks 1 0 0 (c y))

variable {P c : Y → Matrix HI HI ℂ}
  {W : ℝ → ↥(STW59.Gen.sphereEven n) → Y → Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ}
  {ξ : ↥(STW59.Gen.sphereOdd n) → Fin (n + 1) → ℂ}
  {g : ↥(STW59.Gen.sphereOdd n) → Matrix (Fin n) (Fin n) ℂ}

theorem northFG_star_mul (hξ : IsCapDatum n ξ) (hg1 : ∀ x, (g x)ᴴ * g x = 1)
    {x : ↥(STW59.Gen.sphereOdd n)} (hx : 0 ≤ capHeight n x) :
    (northFG n HI ξ g x)ᴴ * northFG n HI ξ g x = 1 := by
  have hN : ξ x (Fin.last n) ≠ -1 := ne_neg_one_of_nonneg_re (by rw [hξ.last]; exact hx)
  exact frameAmb_star_mul (mul_star_mul_of_unitary
    (frameNorth_conjTranspose_mul_self (isFrameDatum_ePole (hξ.mem x) hN))
    (extTop_conjTranspose_mul_self (hg1 x)))

theorem northFG_conj (hξ : IsCapDatum n ξ) (hg2 : ∀ x, g x * (g x)ᴴ = 1)
    (P : Y → Matrix HI HI ℂ) (y : Y) {x : ↥(STW59.Gen.sphereOdd n)} (hx : 0 ≤ capHeight n x) :
    northFG n HI ξ g x * bigE n P y * (northFG n HI ξ g x)ᴴ = bigF n P (ξ x) y := by
  have hN : ξ x (Fin.last n) ≠ -1 := ne_neg_one_of_nonneg_re (by rw [hξ.last]; exact hx)
  refine frameAmb_conj_bigE P y ?_
  rw [Matrix.conjTranspose_mul]
  calc frameNorth (ePole n) (ξ x) * extTop n (g x) * (1 - rk1 (ePole n) (ePole n))
        * ((extTop n (g x))ᴴ * (frameNorth (ePole n) (ξ x))ᴴ)
      = frameNorth (ePole n) (ξ x)
          * (extTop n (g x) * (1 - rk1 (ePole n) (ePole n)) * (extTop n (g x))ᴴ)
          * (frameNorth (ePole n) (ξ x))ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 - rk1 (ξ x) (ξ x) := by
        rw [extTop_conj_compl (hg2 x), frameNorth_conj_eq_compl (hξ.mem x) hN]

theorem continuousAt_northFG (hξ : IsCapDatum n ξ) (hgc : Continuous g)
    {q₀ : ↥(STW59.Gen.sphereOdd n) × Y} (hq : 0 ≤ capHeight n q₀.1) :
    ContinuousAt (fun q : ↥(STW59.Gen.sphereOdd n) × Y => northFG n HI ξ g q.1) q₀ := by
  have hN : ξ q₀.1 (Fin.last n) ≠ -1 := ne_neg_one_of_nonneg_re (by rw [hξ.last]; exact hq)
  have hopenN : IsOpen {x : ↥(STW59.Gen.sphereOdd n) | ξ x (Fin.last n) ≠ -1} :=
    isOpen_ne.preimage ((continuous_apply (Fin.last n)).comp hξ.continuous)
  have hfr : ContinuousAt (fun x : ↥(STW59.Gen.sphereOdd n) => frameNorth (ePole n) (ξ x)) q₀.1 :=
    (continuousOn_frameNorth_comp hξ.continuous hξ.mem).continuousAt (hopenN.mem_nhds hN)
  have hc : ContinuousAt (fun x : ↥(STW59.Gen.sphereOdd n) =>
      frameNorth (ePole n) (ξ x) * extTop n (g x)) q₀.1 :=
    hfr.mul ((continuous_extTop (n := n)).continuousAt.comp hgc.continuousAt)
  exact ((continuous_frameAmb (n := n) (HI := HI)).continuousAt).comp (hc.comp continuousAt_fst)

/-- **The gauged seam.**  On the equator the two hemisphere fields agree. -/
theorem southAtG_eq_northFG (hξ : IsCapDatum n ξ) (hg1 : ∀ x, (g x)ᴴ * g x = 1)
    (hg2 : ∀ x, g x * (g x)ᴴ = 1) (hP : ∀ y, P y * P y = P y) (hPs : ∀ y, (P y)ᴴ = P y)
    (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hW1 : ∀ x, capHeight n x = 0 → ∀ y,
      W 1 (dirPt n x) y = Matrix.fromBlocks ((g x)ᴴ * genU2 n (ξ x)) 0 0 (c y))
    (x : ↥(STW59.Gen.sphereOdd n)) (y : Y) (hq : capHeight n x = 0) :
    southAtG n P c W ξ x y = northFG n HI ξ g x := by
  have hxm := hξ.mem x
  have hlast : (ξ x (Fin.last n)).re = 0 := by rw [hξ.last]; exact hq
  have hN : ξ x (Fin.last n) ≠ -1 := ne_neg_one_of_re_eq_zero hlast
  have hS : ξ x (Fin.last n) ≠ 1 := ne_one_of_re_eq_zero hlast
  have hPc : P y * c y = c y := proj_mul_of_partial (hc1 y) (hc2 y) (hP y)
  have hU1 : (genU2 n (ξ x))ᴴ * genU2 n (ξ x) = 1 := genU2_conjTranspose_mul_self n hxm hN hS
  have hU2 : genU2 n (ξ x) * (genU2 n (ξ x))ᴴ = 1 := genU2_mul_conjTranspose n hxm hN hS
  have hT1 : ((g x)ᴴ * genU2 n (ξ x))ᴴ * ((g x)ᴴ * genU2 n (ξ x)) = 1 := by
    have hgx : ((g x)ᴴ)ᴴ * (g x)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      exact hg2 x
    exact mul_star_mul_of_unitary hgx hU1
  have hT2 : (g x)ᴴ * genU2 n (ξ x) * ((g x)ᴴ * genU2 n (ξ x))ᴴ = 1 := by
    have hgx : (g x)ᴴ * ((g x)ᴴ)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      exact hg1 x
    exact mul_mul_star_of_unitary hgx hU2
  have hsplit : W (capTime n x) (dirPt n x) y
      = Matrix.fromBlocks ((g x)ᴴ * genU2 n (ξ x)) 0 0 (P y) * Matrix.fromBlocks 1 0 0 (c y) := by
    rw [capTime_eq_one hq, hW1 x hq y, fromBlocks_diag_mul_rect, Matrix.mul_one, hPc]
  have htop := isCornerUnit_topBlock (n := n) (P := P) (y := y) hT1 hT2 (hP y) (hPs y)
  have hcb := isCornerUnit_coBlock (n := n) (P := P) (y := y) (hc1 y) (hc2 y)
  have hCu : (coframeAmb n HI (c y + (1 - P y)))ᴴ * coframeAmb n HI (c y + (1 - P y)) = 1 := by
    have := extAmb_conjTranspose_mul_self hcb (hP y) (hPs y)
    rwa [extAmb_coBlock] at this
  have hext : extAmb n P y (W (capTime n x) (dirPt n x) y)
      = frameAmb n HI ((extTop n (g x))ᴴ * genU n (ξ x)) * coframeAmb n HI (c y + (1 - P y)) := by
    rw [hsplit, extAmb_mul htop hcb (hP y), extAmb_topBlock, extAmb_coBlock, extTop_mul,
      ← extTop_conjTranspose, extTop_genU2 hxm hN hS]
  have hcomm : (coframeAmb n HI (c y + (1 - P y)))ᴴ
        * (frameAmb n HI ((extTop n (g x))ᴴ * genU n (ξ x)))ᴴ
      = (frameAmb n HI ((extTop n (g x))ᴴ * genU n (ξ x)))ᴴ
        * (coframeAmb n HI (c y + (1 - P y)))ᴴ := by
    rw [coframeAmb_conjTranspose, frameAmb_conjTranspose, frameAmb_comm_coframeAmb]
  rw [southAtG, hext, extAmb_coBlock, Matrix.conjTranspose_mul]
  calc frameAmb n HI (frameSouth (ePole n) (ξ x))
        * ((coframeAmb n HI (c y + (1 - P y)))ᴴ
          * (frameAmb n HI ((extTop n (g x))ᴴ * genU n (ξ x)))ᴴ)
        * coframeAmb n HI (c y + (1 - P y))
      = frameAmb n HI (frameSouth (ePole n) (ξ x))
          * (frameAmb n HI ((extTop n (g x))ᴴ * genU n (ξ x)))ᴴ
          * ((coframeAmb n HI (c y + (1 - P y)))ᴴ * coframeAmb n HI (c y + (1 - P y))) := by
        rw [hcomm]
        simp only [Matrix.mul_assoc]
    _ = northFG n HI ξ g x := by
        rw [hCu, Matrix.mul_one, frameAmb_conjTranspose, frameAmb_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
          frameSouth_mul_genU_conjTranspose hxm hS, northFG]

theorem southAtG_star_mul (hξ : IsCapDatum n ξ) (hP : ∀ y, P y * P y = P y)
    (hPs : ∀ y, (P y)ᴴ = P y) (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hWu : ∀ t v y, IsCornerUnit n P y (W t v y))
    (x : ↥(STW59.Gen.sphereOdd n)) (y : Y) (hq : capHeight n x ≤ 0) :
    (southAtG n P c W ξ x y)ᴴ * southAtG n P c W ξ x y = 1 := by
  have hS : ξ x (Fin.last n) ≠ 1 := ne_one_of_nonpos_re (by rw [hξ.last]; exact hq)
  have h1 : (frameAmb n HI (frameSouth (ePole n) (ξ x)))ᴴ
      * frameAmb n HI (frameSouth (ePole n) (ξ x)) = 1 :=
    frameAmb_star_mul
      (frameSouth_conjTranspose_mul_self (unit_ePole n) (isFrameDatum_neg_ePole (hξ.mem x) hS))
  have h2 : ((extAmb n P y (W (capTime n x) (dirPt n x) y))ᴴ)ᴴ
      * (extAmb n P y (W (capTime n x) (dirPt n x) y))ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact extAmb_mul_conjTranspose (hWu _ _ _) (hP y) (hPs y)
  have h3 : (extAmb n P y (Matrix.fromBlocks 1 0 0 (c y)))ᴴ
      * extAmb n P y (Matrix.fromBlocks 1 0 0 (c y)) = 1 :=
    extAmb_conjTranspose_mul_self (isCornerUnit_coBlock (n := n) (hc1 y) (hc2 y)) (hP y) (hPs y)
  exact mul_star_mul_of_unitary (mul_star_mul_of_unitary h1 h2) h3

theorem southAtG_conj (hξ : IsCapDatum n ξ) (hP : ∀ y, P y * P y = P y)
    (hPs : ∀ y, (P y)ᴴ = P y) (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hWu : ∀ t v y, IsCornerUnit n P y (W t v y))
    (x : ↥(STW59.Gen.sphereOdd n)) (y : Y) (hq : capHeight n x ≤ 0) :
    southAtG n P c W ξ x y * bigE n P y * (southAtG n P c W ξ x y)ᴴ = bigF n P (ξ x) y := by
  have hS : ξ x (Fin.last n) ≠ 1 := ne_one_of_nonpos_re (by rw [hξ.last]; exact hq)
  have h2 : (extAmb n P y (W (capTime n x) (dirPt n x) y))ᴴ
      * ((extAmb n P y (W (capTime n x) (dirPt n x) y))ᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact extAmb_conjTranspose_mul_self (hWu _ _ _) (hP y) (hPs y)
  have h3 : extAmb n P y (Matrix.fromBlocks 1 0 0 (c y))
      * (extAmb n P y (Matrix.fromBlocks 1 0 0 (c y)))ᴴ = 1 :=
    extAmb_mul_conjTranspose (isCornerUnit_coBlock (n := n) (hc1 y) (hc2 y)) (hP y) (hPs y)
  have h4 : (extAmb n P y (W (capTime n x) (dirPt n x) y))ᴴ * bigE n P y
      = bigE n P y * (extAmb n P y (W (capTime n x) (dirPt n x) y))ᴴ :=
    conjTranspose_comm_of_comm (conjTranspose_bigE (hPs y))
      (extAmb_comm_bigE (hWu _ _ _) (hP y))
  have h5 : extAmb n P y (Matrix.fromBlocks 1 0 0 (c y)) * bigE n P y
      = bigE n P y * extAmb n P y (Matrix.fromBlocks 1 0 0 (c y)) :=
    extAmb_comm_bigE (isCornerUnit_coBlock (n := n) (hc1 y) (hc2 y)) (hP y)
  have h6 : frameAmb n HI (frameSouth (ePole n) (ξ x)) * bigE n P y
      * (frameAmb n HI (frameSouth (ePole n) (ξ x)))ᴴ = bigF n P (ξ x) y :=
    frameAmb_conj_bigE P y (frameSouth_conj_eq_compl (hξ.mem x) hS)
  simp only [southAtG]
  exact conj_triple h2 h3 h4 h5 h6

theorem continuousAt_southFG (hξ : IsCapDatum n ξ) (hPc : Continuous P) (hcc : Continuous c)
    (hWc : Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) × Y => W r.1 r.2.1 r.2.2)
    (hW0 : ∀ v y, W 0 v y = cornerE n P y)
    {q₀ : ↥(STW59.Gen.sphereOdd n) × Y} (hq : capHeight n q₀.1 ≤ 0) :
    ContinuousAt (fun q : ↥(STW59.Gen.sphereOdd n) × Y => southAtG n P c W ξ q.1 q.2) q₀ := by
  have hS : ξ q₀.1 (Fin.last n) ≠ 1 := ne_one_of_nonpos_re (by rw [hξ.last]; exact hq)
  have hopenS : IsOpen {x : ↥(STW59.Gen.sphereOdd n) | ξ x (Fin.last n) ≠ 1} :=
    isOpen_ne.preimage ((continuous_apply (Fin.last n)).comp hξ.continuous)
  have h1 : ContinuousAt (fun q : ↥(STW59.Gen.sphereOdd n) × Y =>
      frameAmb n HI (frameSouth (ePole n) (ξ q.1))) q₀ :=
    ((continuous_frameAmb (n := n) (HI := HI)).continuousAt).comp
      (((continuousOn_frameSouth_comp hξ.continuous hξ.mem).continuousAt
        (hopenS.mem_nhds hS)).comp continuousAt_fst)
  have hcorr : ContinuousAt (fun q : ↥(STW59.Gen.sphereOdd n) × Y =>
      W (capTime n q.1) (dirPt n q.1) q.2) q₀ := by
    rcases lt_or_ge (capHeight n q₀.1) (-(1 / 2)) with hlt | hge
    · have hopen : IsOpen {q : ↥(STW59.Gen.sphereOdd n) × Y | capHeight n q.1 < -(1 / 2)} :=
        isOpen_lt ((continuous_capHeight n).comp continuous_fst) continuous_const
      have heq : (fun q : ↥(STW59.Gen.sphereOdd n) × Y => W (capTime n q.1) (dirPt n q.1) q.2)
          =ᶠ[nhds q₀] fun q : ↥(STW59.Gen.sphereOdd n) × Y => cornerE n P q.2 :=
        Filter.eventually_of_mem (hopen.mem_nhds hlt) fun q hq' => by
          show W (capTime n q.1) (dirPt n q.1) q.2 = cornerE n P q.2
          rw [capTime_eq_zero (le_of_lt hq'), hW0]
      exact ContinuousAt.congr
        ((continuous_cornerE n hPc).continuousAt.comp continuousAt_snd) heq.symm
    · have hlt1 : ((q₀.1 : Fin (n + 1) → ℂ) (Fin.last n)).re ^ 2 < 1 := by
        have h0 : -(1 / 2) ≤ capHeight n q₀.1 := hge
        show capHeight n q₀.1 ^ 2 < 1
        nlinarith
      have hne : equatorInv n (q₀.1 : Fin (n + 1) → ℂ) ≠ 0 := equatorInv_ne_zero q₀.1.2 hlt1
      exact hWc.continuousAt.comp
        (((continuous_capTime n).continuousAt.comp continuousAt_fst).prodMk
          (((continuousAt_dirPt hne).comp continuousAt_fst).prodMk continuousAt_snd))
  have h2 : ContinuousAt (fun q : ↥(STW59.Gen.sphereOdd n) × Y =>
      (extAmb n P q.2 (W (capTime n q.1) (dirPt n q.1) q.2))ᴴ) q₀ :=
    (continuous_id.matrix_conjTranspose.continuousAt).comp
      (continuousAt_extAmb n hPc hcorr continuousAt_snd)
  have h3 : ContinuousAt (fun q : ↥(STW59.Gen.sphereOdd n) × Y =>
      extAmb n P q.2 (Matrix.fromBlocks 1 0 0 (c q.2))) q₀ :=
    continuousAt_extAmb n hPc ((Continuous.matrix_fromBlocks continuous_const continuous_const
      continuous_const hcc).continuousAt.comp continuousAt_snd) continuousAt_snd
  exact (h1.mul h2).mul h3

/-- **The analytic half of Corollary 4 at rank `n`, gauged and pulled back.**  A null-homotopy
inside the corner whose end is `(g x)ᴴ · genU2 (ξ x) ⊕ c` on the equator produces a continuous
unitary field of the ambient carrying the constant complement to the complement of `ξ x`. -/
theorem exists_unitary_field_of_nullHomotopy_gauged (hξ : IsCapDatum n ξ) (hgc : Continuous g)
    (hg1 : ∀ x, (g x)ᴴ * g x = 1) (hg2 : ∀ x, g x * (g x)ᴴ = 1)
    (hPc : Continuous P) (hP : ∀ y, P y * P y = P y) (hPs : ∀ y, (P y)ᴴ = P y)
    (hcc : Continuous c) (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hWc : Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) × Y => W r.1 r.2.1 r.2.2)
    (hWu : ∀ t v y, IsCornerUnit n P y (W t v y))
    (hW0 : ∀ v y, W 0 v y = cornerE n P y)
    (hW1 : ∀ x, capHeight n x = 0 → ∀ y,
      W 1 (dirPt n x) y = Matrix.fromBlocks ((g x)ᴴ * genU2 n (ξ x)) 0 0 (c y)) :
    ∃ G : ↥(STW59.Gen.sphereOdd n) × Y → Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ,
      Continuous G ∧ (∀ q, (G q)ᴴ * G q = 1) ∧
      (∀ q, G q * bigE n P q.2 * (G q)ᴴ = bigF n P (ξ q.1) q.2) := by
  refine ⟨fun q => if 0 ≤ capHeight n q.1 then northFG n HI ξ g q.1
    else southAtG n P c W ξ q.1 q.2, ?_, ?_, ?_⟩
  · refine continuous_if_le continuous_const ((continuous_capHeight n).comp continuous_fst)
      (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
    · exact (continuousAt_northFG hξ hgc hq).continuousWithinAt
    · exact (continuousAt_southFG hξ hPc hcc hWc hW0 hq).continuousWithinAt
    · exact (southAtG_eq_northFG hξ hg1 hg2 hP hPs hc1 hc2 hW1 q.1 q.2 hq.symm).symm
  · intro q
    dsimp only
    split_ifs with h
    · exact northFG_star_mul hξ hg1 h
    · exact southAtG_star_mul hξ hP hPs hc1 hc2 hWu q.1 q.2 (le_of_lt (not_le.mp h))
  · intro q
    dsimp only
    split_ifs with h
    · exact northFG_conj hξ hg2 P q.2 h
    · exact southAtG_conj hξ hP hPs hc1 hc2 hWu q.1 q.2 (le_of_lt (not_le.mp h))

end Fields

end

end Gen
end LIX
end GroupApproximation

open GroupApproximation.LIX.Gen

#audit_axioms equatorEmb_equatorInv
#audit_axioms norm_sq_equatorInv
#audit_axioms equatorEmb_dirPt
#audit_axioms extTop_genU2
#audit_axioms southAtG_eq_northFG
#audit_axioms exists_unitary_field_of_nullHomotopy_gauged
