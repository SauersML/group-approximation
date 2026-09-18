import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTCliffordSystem
import Mathlib.Tactic.LinearCombination

/-!
# The Clifford functional calculus behind the Bott element

Lane TWWUCT-D (WO-TWWUCT-D), a foundational layer for the Higson--Kasparov theorem
(Higson--Kasparov, Invent. Math. 144 (2001), Thm. 1.1 / 8.5), which is the UCT input of
`thm:fixed-radical-membership` in `non_mf_group_notes.tex`.

The Bott asymptotic morphism of Higson--Kasparov--Trout (Adv. Math. 135 (1998), §2--§4) and
of Higson--Kasparov (2001, §5--§6) sends `f ∈ 𝒮 = C₀(ℝ)` to `f(t⁻¹ C)`, where `C` is the Clifford
variable.  Pointwise the Clifford variable `c = c(x)` satisfies `c² = R²·1` with
`R = √(x₁² + ‖x₂‖²)`, so the functional calculus reduces to the two-point formula

  `f(c) = ½(f(R) + f(-R))·1 + (f(R) - f(-R))/(2R)·c`.

We prove that this formula is a ⋆-homomorphism `(ℝ → ℂ) →⋆ₙₐ[ℂ] C`, compatible with the
orthogonal action and the grading (odd functions go to odd elements), compute it on the Gaussian
generators `e^{-s²}` and `s e^{-s²}` of `𝒮` (HKT 1998, §4), bound its norm, and record the basic
affine displacement estimate `‖c(s(t, π_g h + b_g)) - π_g c(s(t, h))‖ ≤ |s| ‖b_g‖` that drives
asymptotic equivariance (HK 2001, §6).
-/

namespace GroupApproximation.Full.TWWUCT

namespace HigsonKasparov

noncomputable section

open CliffordSystem
open scoped InnerProductSpace

universe v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-! ### Elementary Clifford identities -/

theorem clifford_zero : (clifford (0 : ℝ × H) : C) = 0 := by
  have h := clifford_smul (C := C) (0 : ℝ) (0 : ℝ × H)
  rwa [zero_smul, Complex.ofReal_zero, zero_smul] at h

/-- The Clifford anticommutation relation `c(x)c(y) + c(y)c(x) = 2⟨x, y⟩·1` for `ℝ ⊕ H`
(HKT 1998, §2). -/
theorem clifford_anticomm (x y : ℝ × H) :
    (clifford x : C) * clifford y + clifford y * clifford x =
      ((2 * (x.1 * y.1 + ⟪x.2, y.2⟫_ℝ) : ℝ) : ℂ) • (1 : C) := by
  have hxy := clifford_mul_self (C := C) (x + y)
  have hscal : (x + y).1 ^ 2 + ‖(x + y).2‖ ^ 2 =
      (x.1 ^ 2 + ‖x.2‖ ^ 2) + (y.1 ^ 2 + ‖y.2‖ ^ 2) + 2 * (x.1 * y.1 + ⟪x.2, y.2⟫_ℝ) := by
    rw [Prod.fst_add, Prod.snd_add, norm_add_sq_real]
    ring
  have key : ((((x.1 ^ 2 + ‖x.2‖ ^ 2) + (y.1 ^ 2 + ‖y.2‖ ^ 2) +
        2 * (x.1 * y.1 + ⟪x.2, y.2⟫_ℝ) : ℝ) : ℂ) • (1 : C)) =
      ((x.1 ^ 2 + ‖x.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) + ((y.1 ^ 2 + ‖y.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) +
        ((2 * (x.1 * y.1 + ⟪x.2, y.2⟫_ℝ) : ℝ) : ℂ) • (1 : C) := by
    rw [← add_smul, ← add_smul, ← Complex.ofReal_add, ← Complex.ofReal_add]
  rw [hscal, key, clifford_add, add_mul, mul_add, mul_add, clifford_mul_self (C := C) x,
    clifford_mul_self (C := C) y] at hxy
  calc (clifford x : C) * clifford y + clifford y * clifford x
      = (((x.1 ^ 2 + ‖x.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) + clifford x * clifford y +
          (clifford y * clifford x + ((y.1 ^ 2 + ‖y.2‖ ^ 2 : ℝ) : ℂ) • (1 : C))) -
          ((x.1 ^ 2 + ‖x.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) -
          ((y.1 ^ 2 + ‖y.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) := by abel
    _ = (((x.1 ^ 2 + ‖x.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) +
          ((y.1 ^ 2 + ‖y.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) +
          ((2 * (x.1 * y.1 + ⟪x.2, y.2⟫_ℝ) : ℝ) : ℂ) • (1 : C)) -
          ((x.1 ^ 2 + ‖x.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) -
          ((y.1 ^ 2 + ‖y.2‖ ^ 2 : ℝ) : ℂ) • (1 : C) := by rw [hxy]
    _ = ((2 * (x.1 * y.1 + ⟪x.2, y.2⟫_ℝ) : ℝ) : ℂ) • (1 : C) := by abel

/-- The Clifford radius `R(x) = √(x₁² + ‖x₂‖²)`, so that `c(x)² = R(x)²·1`. -/
def cliffRadius (x : ℝ × H) : ℝ :=
  Real.sqrt (x.1 ^ 2 + ‖x.2‖ ^ 2)

theorem cliffRadius_nonneg (x : ℝ × H) : 0 ≤ cliffRadius x :=
  Real.sqrt_nonneg _

theorem cliffRadius_sq (x : ℝ × H) : cliffRadius x ^ 2 = x.1 ^ 2 + ‖x.2‖ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg x.1) (sq_nonneg ‖x.2‖))

theorem clifford_mul_self_cliffRadius (x : ℝ × H) :
    (clifford x : C) * clifford x = (cliffRadius x : ℂ) ^ 2 • (1 : C) := by
  rw [clifford_mul_self, ← Complex.ofReal_pow, cliffRadius_sq]

theorem clifford_eq_zero_of_cliffRadius_eq_zero {x : ℝ × H} (hx : cliffRadius x = 0) :
    (clifford x : C) = 0 := by
  have h1 : |x.1| ≤ cliffRadius x :=
    Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg ‖x.2‖))
  have h2 : |‖x.2‖| ≤ cliffRadius x :=
    Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg x.1))
  rw [abs_norm] at h2
  have h3 := norm_clifford_le (C := C) x
  exact norm_le_zero_iff.mp (by linarith)

/-- `‖c(x)‖ = R(x)` in a nonzero C⋆-algebra (C⋆-identity). -/
theorem norm_clifford [Nontrivial C] (x : ℝ × H) : ‖(clifford x : C)‖ = cliffRadius x := by
  have h : ‖(clifford x : C)‖ * ‖(clifford x : C)‖ = x.1 ^ 2 + ‖x.2‖ ^ 2 := by
    rw [← CStarRing.norm_star_mul_self, star_clifford, clifford_mul_self, norm_smul, norm_one,
      mul_one, Complex.norm_of_nonneg (add_nonneg (sq_nonneg x.1) (sq_nonneg ‖x.2‖))]
  unfold cliffRadius
  rw [← h, Real.sqrt_mul_self (norm_nonneg _)]

/-! ### The two-point functional calculus -/

/-- The even coefficient `½(f(r) + f(-r))`. -/
def evenCoeff (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  (f r + f (-r)) / 2

/-- The odd coefficient `(f(r) - f(-r))/(2r)` (zero at `r = 0`). -/
def oddCoeff (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  (f r - f (-r)) / (2 * (r : ℂ))

variable (C) in
/-- The Clifford functional calculus `f ↦ f(c(x))` at a point `x ∈ ℝ ⊕ H`, via the two-point
formula for an element with `c² = R²·1` (HKT 1998, §4; HK 2001, §5). -/
def bottCalc (f : ℝ → ℂ) (x : ℝ × H) : C :=
  evenCoeff f (cliffRadius x) • (1 : C) + oddCoeff f (cliffRadius x) • clifford x

/-- Multiplication rule in the two-dimensional algebra spanned by `1` and `c`, `c² = ρ·1`. -/
theorem two_point_mul {c : C} {ρ : ℂ} (hc : c * c = ρ • (1 : C)) (p q p' q' : ℂ) :
    (p • (1 : C) + q • c) * (p' • (1 : C) + q' • c) =
      (p * p' + q * q' * ρ) • (1 : C) + (p * q' + q * p') • c := by
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, one_mul, mul_one, one_mul, hc, smul_smul, add_smul, add_smul]
  abel

theorem evenCoeff_mul (f g : ℝ → ℂ) (r : ℝ) :
    evenCoeff (f * g) r =
      evenCoeff f r * evenCoeff g r + oddCoeff f r * oddCoeff g r * (r : ℂ) ^ 2 := by
  show (f r * g r + f (-r) * g (-r)) / 2 =
    (f r + f (-r)) / 2 * ((g r + g (-r)) / 2) +
      (f r - f (-r)) / (2 * (r : ℂ)) * ((g r - g (-r)) / (2 * (r : ℂ))) * (r : ℂ) ^ 2
  rcases eq_or_ne r 0 with rfl | hr
  · rw [neg_zero, Complex.ofReal_zero]
    ring
  · have h : (r : ℂ) * (r : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr)
    linear_combination
      (-(f r - f (-r)) * (g r - g (-r)) / 4 * (1 + (r : ℂ) * (r : ℂ)⁻¹)) * h

theorem oddCoeff_mul (f g : ℝ → ℂ) (r : ℝ) :
    oddCoeff (f * g) r = evenCoeff f r * oddCoeff g r + oddCoeff f r * evenCoeff g r := by
  show (f r * g r - f (-r) * g (-r)) / (2 * (r : ℂ)) =
    (f r + f (-r)) / 2 * ((g r - g (-r)) / (2 * (r : ℂ))) +
      (f r - f (-r)) / (2 * (r : ℂ)) * ((g r + g (-r)) / 2)
  ring

theorem evenCoeff_add (f g : ℝ → ℂ) (r : ℝ) :
    evenCoeff (f + g) r = evenCoeff f r + evenCoeff g r := by
  show (f r + g r + (f (-r) + g (-r))) / 2 = (f r + f (-r)) / 2 + (g r + g (-r)) / 2
  ring

theorem oddCoeff_add (f g : ℝ → ℂ) (r : ℝ) :
    oddCoeff (f + g) r = oddCoeff f r + oddCoeff g r := by
  show (f r + g r - (f (-r) + g (-r))) / (2 * (r : ℂ)) =
    (f r - f (-r)) / (2 * (r : ℂ)) + (g r - g (-r)) / (2 * (r : ℂ))
  ring

theorem evenCoeff_smul (a : ℂ) (f : ℝ → ℂ) (r : ℝ) :
    evenCoeff (a • f) r = a * evenCoeff f r := by
  show (a * f r + a * f (-r)) / 2 = a * ((f r + f (-r)) / 2)
  ring

theorem oddCoeff_smul (a : ℂ) (f : ℝ → ℂ) (r : ℝ) :
    oddCoeff (a • f) r = a * oddCoeff f r := by
  show (a * f r - a * f (-r)) / (2 * (r : ℂ)) = a * ((f r - f (-r)) / (2 * (r : ℂ)))
  ring

theorem evenCoeff_zero (r : ℝ) : evenCoeff 0 r = 0 := by
  show ((0 : ℂ) + 0) / 2 = 0
  ring

theorem oddCoeff_zero (r : ℝ) : oddCoeff 0 r = 0 := by
  show ((0 : ℂ) - 0) / (2 * (r : ℂ)) = 0
  ring

theorem evenCoeff_one (r : ℝ) : evenCoeff 1 r = 1 := by
  show ((1 : ℂ) + 1) / 2 = 1
  norm_num

theorem oddCoeff_one (r : ℝ) : oddCoeff 1 r = 0 := by
  show ((1 : ℂ) - 1) / (2 * (r : ℂ)) = 0
  ring

theorem evenCoeff_star (f : ℝ → ℂ) (r : ℝ) :
    evenCoeff (star f) r = star (evenCoeff f r) := by
  show (star (f r) + star (f (-r))) / 2 = star ((f r + f (-r)) / 2)
  rw [star_div₀, star_add, star_ofNat]

theorem oddCoeff_star (f : ℝ → ℂ) (r : ℝ) :
    oddCoeff (star f) r = star (oddCoeff f r) := by
  have hr : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  show (star (f r) - star (f (-r))) / (2 * (r : ℂ)) =
    star ((f r - f (-r)) / (2 * (r : ℂ)))
  rw [star_div₀, star_sub, star_mul', star_ofNat, hr]

theorem evenCoeff_comp_neg (f : ℝ → ℂ) (r : ℝ) :
    evenCoeff (fun s => f (-s)) r = evenCoeff f r := by
  show (f (-r) + f (-(-r))) / 2 = (f r + f (-r)) / 2
  rw [neg_neg]
  ring

theorem oddCoeff_comp_neg (f : ℝ → ℂ) (r : ℝ) :
    oddCoeff (fun s => f (-s)) r = -oddCoeff f r := by
  show (f (-r) - f (-(-r))) / (2 * (r : ℂ)) = -((f r - f (-r)) / (2 * (r : ℂ)))
  rw [neg_neg]
  ring

/-! ### The functional calculus is a ⋆-homomorphism -/

theorem bottCalc_mul (f g : ℝ → ℂ) (x : ℝ × H) :
    bottCalc C (f * g) x = bottCalc C f x * bottCalc C g x := by
  unfold bottCalc
  rw [two_point_mul (clifford_mul_self_cliffRadius (C := C) x),
    evenCoeff_mul f g (cliffRadius x), oddCoeff_mul f g (cliffRadius x)]

theorem bottCalc_add (f g : ℝ → ℂ) (x : ℝ × H) :
    bottCalc C (f + g) x = bottCalc C f x + bottCalc C g x := by
  unfold bottCalc
  rw [evenCoeff_add, oddCoeff_add, add_smul, add_smul]
  abel

theorem bottCalc_smul (a : ℂ) (f : ℝ → ℂ) (x : ℝ × H) :
    bottCalc C (a • f) x = a • bottCalc C f x := by
  unfold bottCalc
  rw [evenCoeff_smul, oddCoeff_smul, mul_smul, mul_smul, smul_add]

theorem bottCalc_zero (x : ℝ × H) : bottCalc C (0 : ℝ → ℂ) x = 0 := by
  unfold bottCalc
  rw [evenCoeff_zero, oddCoeff_zero, zero_smul, zero_smul, add_zero]

theorem bottCalc_one (x : ℝ × H) : bottCalc C (1 : ℝ → ℂ) x = 1 := by
  unfold bottCalc
  rw [evenCoeff_one, oddCoeff_one, one_smul, zero_smul, add_zero]

theorem star_bottCalc (f : ℝ → ℂ) (x : ℝ × H) :
    star (bottCalc C f x) = bottCalc C (star f) x := by
  unfold bottCalc
  rw [star_add, star_smul, star_smul, star_one, star_clifford, evenCoeff_star, oddCoeff_star]

variable (C) in
/-- The pointwise Bott functional calculus `f ↦ f(c(x))` as a non-unital ⋆-homomorphism
(HKT 1998, §4; HK 2001, §5). -/
def bottCalcHom (x : ℝ × H) : (ℝ → ℂ) →⋆ₙₐ[ℂ] C where
  toFun f := bottCalc C f x
  map_smul' a f := bottCalc_smul a f x
  map_zero' := bottCalc_zero x
  map_add' f g := bottCalc_add f g x
  map_mul' f g := bottCalc_mul f g x
  map_star' f := (star_bottCalc f x).symm

theorem bottCalcHom_apply (x : ℝ × H) (f : ℝ → ℂ) : bottCalcHom C x f = bottCalc C f x :=
  rfl

/-! ### Covariance and grading -/

theorem cliffRadius_orth (U : H ≃ₗᵢ[ℝ] H) (x : ℝ × H) :
    cliffRadius (x.1, U x.2) = cliffRadius x := by
  show Real.sqrt (x.1 ^ 2 + ‖U x.2‖ ^ 2) = Real.sqrt (x.1 ^ 2 + ‖x.2‖ ^ 2)
  rw [LinearIsometryEquiv.norm_map]

/-- The functional calculus intertwines the orthogonal action (HKT 1998, §4). -/
theorem orth_bottCalc (U : H ≃ₗᵢ[ℝ] H) (f : ℝ → ℂ) (x : ℝ × H) :
    orth (C := C) U (bottCalc C f x) = bottCalc C f (x.1, U x.2) := by
  unfold bottCalc
  rw [map_add, map_smul, map_smul, map_one, orth_clifford, cliffRadius_orth U x]

/-- The grading acts on the functional calculus by `f ↦ f(-·)`; odd functions give odd elements
(HKT 1998, §4). -/
theorem grading_bottCalc (f : ℝ → ℂ) (x : ℝ × H) :
    grading (H := H) (C := C) (bottCalc C f x) = bottCalc C (fun s => f (-s)) x := by
  unfold bottCalc
  rw [map_add, map_smul, map_smul, map_one, grading_clifford,
    evenCoeff_comp_neg f (cliffRadius x), oddCoeff_comp_neg f (cliffRadius x), neg_smul,
    smul_neg]

/-! ### The Gaussian generators of `𝒮` -/

/-- The even generator `s ↦ e^{-s²}` of `𝒮 = C₀(ℝ)`. -/
def gaussFn : ℝ → ℂ := fun s => (Real.exp (-s ^ 2) : ℂ)

/-- The odd generator `s ↦ s e^{-s²}` of `𝒮 = C₀(ℝ)`. -/
def oddGaussFn : ℝ → ℂ := fun s => (s : ℂ) * (Real.exp (-s ^ 2) : ℂ)

theorem evenCoeff_gaussFn (r : ℝ) : evenCoeff gaussFn r = (Real.exp (-r ^ 2) : ℂ) := by
  show ((Real.exp (-r ^ 2) : ℂ) + (Real.exp (-(-r) ^ 2) : ℂ)) / 2 = (Real.exp (-r ^ 2) : ℂ)
  rw [neg_sq]
  ring

theorem oddCoeff_gaussFn (r : ℝ) : oddCoeff gaussFn r = 0 := by
  show ((Real.exp (-r ^ 2) : ℂ) - (Real.exp (-(-r) ^ 2) : ℂ)) / (2 * (r : ℂ)) = 0
  rw [neg_sq, sub_self, zero_div]

theorem evenCoeff_oddGaussFn (r : ℝ) : evenCoeff oddGaussFn r = 0 := by
  show ((r : ℂ) * (Real.exp (-r ^ 2) : ℂ) + ((-r : ℝ) : ℂ) * (Real.exp (-(-r) ^ 2) : ℂ)) / 2 = 0
  rw [neg_sq, Complex.ofReal_neg]
  ring

theorem oddCoeff_oddGaussFn {r : ℝ} (hr : r ≠ 0) :
    oddCoeff oddGaussFn r = (Real.exp (-r ^ 2) : ℂ) := by
  show ((r : ℂ) * (Real.exp (-r ^ 2) : ℂ) - ((-r : ℝ) : ℂ) * (Real.exp (-(-r) ^ 2) : ℂ)) /
      (2 * (r : ℂ)) = (Real.exp (-r ^ 2) : ℂ)
  rw [neg_sq, Complex.ofReal_neg,
    div_eq_iff (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hr))]
  ring

/-- The even generator goes to `e^{-(t² + ‖h‖²)}·1` (HKT 1998, §4). -/
theorem bottCalc_gaussFn (x : ℝ × H) :
    bottCalc C gaussFn x = (Real.exp (-(x.1 ^ 2 + ‖x.2‖ ^ 2)) : ℂ) • (1 : C) := by
  unfold bottCalc
  rw [evenCoeff_gaussFn, oddCoeff_gaussFn, zero_smul, add_zero, cliffRadius_sq]

/-- The odd generator goes to `e^{-(t² + ‖h‖²)}·c(t, h)` (HKT 1998, Def. 3.1 and §4). -/
theorem bottCalc_oddGaussFn (x : ℝ × H) :
    bottCalc C oddGaussFn x = (Real.exp (-(x.1 ^ 2 + ‖x.2‖ ^ 2)) : ℂ) • clifford x := by
  unfold bottCalc
  rw [evenCoeff_oddGaussFn, zero_smul, zero_add, ← cliffRadius_sq x]
  rcases eq_or_ne (cliffRadius x) 0 with h | h
  · rw [clifford_eq_zero_of_cliffRadius_eq_zero (C := C) h, smul_zero, smul_zero]
  · rw [oddCoeff_oddGaussFn h]

/-! ### Norm bounds -/

theorem norm_evenCoeff_le (f : ℝ → ℂ) (r : ℝ) :
    ‖evenCoeff f r‖ ≤ (‖f r‖ + ‖f (-r)‖) / 2 := by
  unfold evenCoeff
  rw [norm_div, Complex.norm_two]
  have h := norm_add_le (f r) (f (-r))
  linarith

theorem norm_oddCoeff_smul_clifford_le [Nontrivial C] (f : ℝ → ℂ) (x : ℝ × H) :
    ‖oddCoeff f (cliffRadius x) • (clifford x : C)‖ ≤
      (‖f (cliffRadius x)‖ + ‖f (-cliffRadius x)‖) / 2 := by
  rw [norm_smul, norm_clifford]
  rcases eq_or_lt_of_le (cliffRadius_nonneg x) with h | h
  · rw [← h, mul_zero]
    positivity
  · unfold oddCoeff
    rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_of_nonneg h.le, div_mul_eq_mul_div,
      mul_div_mul_right _ _ h.ne']
    have h' := norm_sub_le (f (cliffRadius x)) (f (-cliffRadius x))
    linarith

/-- `‖f(c(x))‖ ≤ |f(R)| + |f(-R)|`, `R = ‖x‖`. -/
theorem norm_bottCalc_le [Nontrivial C] (f : ℝ → ℂ) (x : ℝ × H) :
    ‖bottCalc C f x‖ ≤ ‖f (cliffRadius x)‖ + ‖f (-cliffRadius x)‖ := by
  have h1 := norm_evenCoeff_le f (cliffRadius x)
  have h2 := norm_oddCoeff_smul_clifford_le (C := C) f x
  have h3 := norm_add_le (evenCoeff f (cliffRadius x) • (1 : C))
    (oddCoeff f (cliffRadius x) • (clifford x : C))
  rw [norm_smul, norm_one, mul_one] at h3
  unfold bottCalc
  linarith

/-! ### Affine displacement (asymptotic equivariance, HK 2001, §6) -/

section Affine

variable {G : Type*} [Group G] (b : AffineIsometricAction G H)

/-- `c(t, π_g h + b_g) = π_g c(t, h) + c(0, b_g)`. -/
theorem clifford_act (t : ℝ) (g : G) (h : H) :
    (clifford (t, b.act g h) : C) =
      orth (C := C) (b.linearPart g) (clifford (t, h)) + clifford ((0 : ℝ), b.cocycle g) := by
  have hpt : ((t, b.act g h) : ℝ × H) = (t, b.linearPart g h) + ((0 : ℝ), b.cocycle g) := by
    rw [b.act_apply, Prod.mk_add_mk, add_zero]
  rw [hpt, clifford_add]
  exact congrArg (fun y : C => y + clifford ((0 : ℝ), b.cocycle g))
    (orth_clifford (C := C) (b.linearPart g) (t, h)).symm

theorem clifford_smul_act_sub (s t : ℝ) (g : G) (h : H) :
    (clifford (s • (t, b.act g h)) : C) - orth (C := C) (b.linearPart g) (clifford (s • (t, h))) =
      (s : ℂ) • clifford ((0 : ℝ), b.cocycle g) := by
  rw [clifford_smul, clifford_smul, map_smul, clifford_act (C := C) b, smul_add,
    add_sub_cancel_left]

/-- The displacement estimate `‖c(s(t, g·h)) - π_g c(s(t, h))‖ ≤ |s| ‖b_g‖`: after rescaling by
`s = t⁻¹ → 0` the affine action becomes asymptotically linear (HK 2001, §6; HKT 1998, §4). -/
theorem norm_clifford_smul_act_sub_le (s t : ℝ) (g : G) (h : H) :
    ‖(clifford (s • (t, b.act g h)) : C) - orth (C := C) (b.linearPart g) (clifford (s • (t, h)))‖ ≤
      |s| * ‖b.cocycle g‖ := by
  have hc : ‖(clifford ((0 : ℝ), b.cocycle g) : C)‖ ≤ |(0 : ℝ)| + ‖b.cocycle g‖ :=
    norm_clifford_le _
  rw [abs_zero, zero_add] at hc
  rw [clifford_smul_act_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hc (abs_nonneg s)

end Affine


end

end HigsonKasparov

end GroupApproximation.Full.TWWUCT
