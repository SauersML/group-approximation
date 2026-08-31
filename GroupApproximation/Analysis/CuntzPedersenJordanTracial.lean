import GroupApproximation.Analysis.CuntzPedersenHermitianSeparation
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

/-!
# Jordan decomposition and the tracial refinement of Cuntz--Pedersen separation

`CuntzPedersenHermitianSeparation` proves the Hahn--Banach half of
Cuntz--Pedersen separation: a self-adjoint element outside the closed real
span of additive self-commutators is detected by a bounded *hermitian tracial*
functional.  That functional is signed.  Turning it into a tracial **state**
is the Jordan-decomposition half, and this file supplies it.

## What is proved unconditionally

* `IsPositiveFunctional.isHermitian` --- a bounded positive functional is
  automatically hermitian.  The proof is the two-parameter positivity test
  `0 ≤ f ((c·1 + y)⋆ (c·1 + y))` read at `c = 1` and `c = i`; no continuous
  functional calculus and no order on the algebra are used.
* `IsPositiveFunctional.eq_zero_of_apply_one_eq_zero` --- a bounded positive
  functional killing the unit is zero.  Same test, read along the two real
  one-parameter families.  This is what makes normalization legitimate.
* `isTracialFunctional_of_unitary_invariant` --- a functional invariant under
  every unitary conjugation is tracial.  This uses Mathlib's
  `CStarAlgebra.exists_sum_four_unitary`: unitaries span a unital
  C-star-algebra.
* `conjFunctional` and its norm: conjugation by a unitary is an isometry of
  the dual which preserves positivity and fixes every tracial functional.
* `isTracialFunctional_jordan_parts` --- **the tracial refinement**.  If `f`
  is tracial and `f = p - q` is a norm-additive Jordan decomposition, then
  *both* `p` and `q` are tracial.  The mechanism is: unitary conjugation
  carries one norm-additive Jordan pair of `f` to another, and uniqueness of
  the norm-additive decomposition then forces the parts to be fixed.
* `normalizedTracialState` --- a nonzero positive tracial functional
  normalizes to a bundled `TracialState`.
* `hasCuntzPedersenSeparation_of_jordan` --- the payoff.  The property
  `HasCuntzPedersenSeparation`, which `CuntzPedersenCoronaObstruction` carries
  as an explicit hypothesis, follows from the *standard literature theorem*:
  existence and uniqueness of the norm-additive Jordan decomposition of a
  bounded hermitian functional (Cuntz--Pedersen, J. Funct. Anal. 33 (1979);
  the underlying Jordan theorem is Takesaki, *Theory of Operator Algebras I*,
  III.4.2).

## Generality achieved, and what remains

The reduction is complete and unconditional for an arbitrary unital
C-star-algebra.  What is *not* proved here is the Jordan decomposition itself:
`HasJordanDecomposition` and `HasUniqueJordanDecomposition` remain explicit
hypotheses.  Their standard proofs pass through the enveloping von Neumann
algebra (normal extension of a functional to `A⋆⋆`, then the support
projection), and Mathlib has neither `A⋆⋆` as a von Neumann algebra nor the
normal-functional theory.  Stating them as named `Prop`s keeps that debt
visible in the dependency surface rather than hiding it inside a bespoke
separation axiom.

The gain over the previous surface is exact: `HasCuntzPedersenSeparation` was
an ad-hoc statement with no literature name; the two hypotheses used here are
verbatim standard theorems, and the *tracial* clause of Cuntz--Pedersen --- the
part with no textbook proof written out in the tracial case --- is now proved
rather than assumed.

`CuntzPedersenJordanModelTest` model-tests all three properties at `A = ℂ`,
where they are proved unconditionally.
-/

namespace GroupApproximation
namespace CuntzPedersenJordanTracial

open CuntzPedersenCoronaObstruction CuntzPedersenTraceZero
  CuntzPedersenHermitianSeparation
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ## Elementary arithmetic in the complex order -/

/-- A nonnegative complex number is the cast of its own real part. -/
theorem eq_ofReal_re_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ((z.re : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp hz).2.symm

/-- The complex order is closed under multiplication.  Stated separately
because `ℂ` is only partially ordered, so the ordered-field lemmas do not
apply. -/
theorem mul_nonneg_complex {z w : ℂ} (hz : 0 ≤ z) (hw : 0 ≤ w) : 0 ≤ z * w := by
  rw [eq_ofReal_re_of_nonneg hz, eq_ofReal_re_of_nonneg hw, ← Complex.ofReal_mul]
  exact Complex.zero_le_real.mpr
    (mul_nonneg (Complex.nonneg_iff.mp hz).1 (Complex.nonneg_iff.mp hw).1)

/-- The complex order is closed under inversion. -/
theorem inv_nonneg_complex {z : ℂ} (hz : 0 ≤ z) : 0 ≤ z⁻¹ := by
  rw [eq_ofReal_re_of_nonneg hz, ← Complex.ofReal_inv]
  exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Complex.nonneg_iff.mp hz).1)

/-- A real affine function which is nonnegative on the whole line is
constant.  This is the only optimization step in the file: it is what turns a
positivity test into the vanishing of a linear coefficient. -/
theorem eq_zero_of_forall_mul_add_nonneg {a b : ℝ} (h : ∀ t : ℝ, 0 ≤ t * a + b) :
    a = 0 := by
  by_contra ha
  have hb := h (-(|b| + 1) / a)
  rw [div_mul_cancel₀ _ ha] at hb
  have habs : b ≤ |b| := le_abs_self b
  linarith

/-! ## Real and imaginary parts of the sesquilinear test terms -/

theorem im_star_mul_self (c : ℂ) : (star c * c).im = 0 := by
  simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem im_star_mul_add_mul (c z v : ℂ) :
    (star c * z + c * v).im = c.re * (z.im + v.im) + c.im * (v.re - z.re) := by
  simp only [Complex.add_im, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem re_star_mul_add_mul_star (c z : ℂ) :
    (star c * z + c * star z).re = 2 * (c.re * z.re + c.im * z.im) := by
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem re_ofReal_mul_I (t : ℝ) : (((t : ℝ) : ℂ) * Complex.I).re = 0 := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem im_ofReal_mul_I (t : ℝ) : (((t : ℝ) : ℂ) * Complex.I).im = t := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-! ## Positive, tracial and hermitian bounded functionals -/

/-- A bounded functional is **positive** when it is nonnegative on every
element `z⋆ z`.  No order on `A` is required: the inequality is the complex
one. -/
def IsPositiveFunctional (f : A →L[ℂ] ℂ) : Prop := ∀ z : A, 0 ≤ f (star z * z)

/-- A bounded functional is **tracial** when it identifies `ab` with `ba`. -/
def IsTracialFunctional (f : A →L[ℂ] ℂ) : Prop := ∀ a b : A, f (a * b) = f (b * a)

/-- A bounded functional is **hermitian** when it intertwines the two
involutions. -/
def IsHermitianFunctional (f : A →L[ℂ] ℂ) : Prop :=
  ∀ a : A, f (star a) = star (f a)

/-- Expansion of the positivity test element `(c·1 + y)⋆ (c·1 + y)`. -/
theorem star_smul_one_add_mul_self (c : ℂ) (y : A) :
    star (c • (1 : A) + y) * (c • (1 : A) + y) =
      (star c * c) • (1 : A) + (star c • y + c • star y) + star y * y := by
  have e1 : (star c • (1 : A)) * (c • (1 : A)) = (star c * c) • (1 : A) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
  have e2 : (star c • (1 : A)) * y = star c • y := by
    rw [smul_mul_assoc, one_mul]
  have e3 : star y * (c • (1 : A)) = c • star y := by
    rw [mul_smul_comm, mul_one]
  rw [star_add, star_smul, star_one, add_mul, mul_add, mul_add, e1, e2, e3]
  abel

/-- The value of a functional on the positivity test element. -/
theorem apply_star_smul_one_add_mul_self (f : A →L[ℂ] ℂ) (c : ℂ) (y : A) :
    f (star (c • (1 : A) + y) * (c • (1 : A) + y)) =
      (star c * c) * f 1 + (star c * f y + c * f (star y)) + f (star y * y) := by
  rw [star_smul_one_add_mul_self]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The two-parameter positivity test satisfied by every positive
functional. -/
theorem IsPositiveFunctional.nonneg_quadratic {f : A →L[ℂ] ℂ}
    (hf : IsPositiveFunctional f) (c : ℂ) (y : A) :
    0 ≤ (star c * c) * f 1 + (star c * f y + c * f (star y)) + f (star y * y) := by
  rw [← apply_star_smul_one_add_mul_self]
  exact hf _

/-- A positive functional is nonnegative at the unit. -/
theorem IsPositiveFunctional.apply_one_nonneg {f : A →L[ℂ] ℂ}
    (hf : IsPositiveFunctional f) : 0 ≤ f 1 := by
  have h := hf 1
  rwa [star_one, one_mul] at h

/-- **A positive bounded functional is hermitian.**  Read the positivity test
at `c = 1` and `c = i` and take imaginary parts. -/
theorem IsPositiveFunctional.isHermitian {f : A →L[ℂ] ℂ}
    (hf : IsPositiveFunctional f) : IsHermitianFunctional f := by
  have h1im : (f 1).im = 0 := (Complex.nonneg_iff.mp hf.apply_one_nonneg).2.symm
  intro y
  have hQim : (f (star y * y)).im = 0 := (Complex.nonneg_iff.mp (hf y)).2.symm
  have hkey : ∀ c : ℂ,
      c.re * ((f y).im + (f (star y)).im)
        + c.im * ((f (star y)).re - (f y).re) = 0 := by
    intro c
    have h := (Complex.nonneg_iff.mp (hf.nonneg_quadratic c y)).2
    have hz : ((star c * c) * f 1).im = 0 := by
      rw [Complex.mul_im, h1im, im_star_mul_self]
      ring
    rw [Complex.add_im, Complex.add_im, hz, im_star_mul_add_mul, hQim] at h
    linarith
  have hone := hkey 1
  have hI := hkey Complex.I
  rw [Complex.one_re, Complex.one_im] at hone
  rw [Complex.I_re, Complex.I_im] at hI
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]
    linarith
  · rw [Complex.star_def, Complex.conj_im]
    linarith

/-- **A positive bounded functional killing the unit is zero.**  Read the
positivity test along the real families `c = t` and `c = it`; the quadratic
term drops out because `f 1 = 0`, so each family is affine in `t`. -/
theorem IsPositiveFunctional.eq_zero_of_apply_one_eq_zero {f : A →L[ℂ] ℂ}
    (hf : IsPositiveFunctional f) (h1 : f 1 = 0) (y : A) : f y = 0 := by
  have hherm : f (star y) = star (f y) := hf.isHermitian y
  have hquad : ∀ c : ℂ,
      0 ≤ 2 * (c.re * (f y).re + c.im * (f y).im) + (f (star y * y)).re := by
    intro c
    have h := hf.nonneg_quadratic c y
    rw [h1, mul_zero, zero_add, hherm] at h
    have hre := (Complex.nonneg_iff.mp h).1
    rw [Complex.add_re, re_star_mul_add_mul_star] at hre
    linarith
  have hA : (f y).re = 0 := by
    have hstep : ∀ t : ℝ, 0 ≤ t * (2 * (f y).re) + (f (star y * y)).re := by
      intro t
      have h := hquad ((t : ℝ) : ℂ)
      rw [Complex.ofReal_re, Complex.ofReal_im] at h
      linarith
    have hzero := eq_zero_of_forall_mul_add_nonneg hstep
    linarith
  have hB : (f y).im = 0 := by
    have hstep : ∀ t : ℝ, 0 ≤ t * (2 * (f y).im) + (f (star y * y)).re := by
      intro t
      have h := hquad (((t : ℝ) : ℂ) * Complex.I)
      rw [re_ofReal_mul_I, im_ofReal_mul_I] at h
      linarith
    have hzero := eq_zero_of_forall_mul_add_nonneg hstep
    linarith
  apply Complex.ext
  · rw [Complex.zero_re]
    exact hA
  · rw [Complex.zero_im]
    exact hB

/-! ## Conjugation of a functional by a unitary -/

/-- Conjugation by a unitary is isometric on the algebra. -/
theorem norm_conj_mem_unitary {u : A} (hu : u ∈ unitary A) (a : A) :
    ‖u * a * star u‖ = ‖a‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
    CStarRing.norm_mem_unitary_mul _ hu]

/-- Conjugation of a bounded functional by a unitary: `conjFunctional hu f`
sends `a` to `f (u a u⋆)`. -/
def conjFunctional {u : A} (hu : u ∈ unitary A) (f : A →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a ↦ f (u * a * star u)
      map_add' := fun a b ↦ by
        simp only [mul_add, add_mul, map_add]
      map_smul' := fun c a ↦ by
        simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply] }
    ‖f‖ fun a ↦ (f.le_opNorm (u * a * star u)).trans_eq
      (by rw [norm_conj_mem_unitary hu])

@[simp] theorem conjFunctional_apply {u : A} (hu : u ∈ unitary A)
    (f : A →L[ℂ] ℂ) (a : A) : conjFunctional hu f a = f (u * a * star u) := rfl

theorem norm_conjFunctional_le {u : A} (hu : u ∈ unitary A) (f : A →L[ℂ] ℂ) :
    ‖conjFunctional hu f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

/-- Conjugating by `u` and then by `u⋆` is the identity. -/
theorem conjFunctional_conjFunctional {u : A} (hu : u ∈ unitary A)
    (f : A →L[ℂ] ℂ) :
    conjFunctional (Unitary.star_mem hu) (conjFunctional hu f) = f := by
  refine ContinuousLinearMap.ext fun a ↦ ?_
  rw [conjFunctional_apply, conjFunctional_apply, star_star]
  congr 1
  calc u * (star u * a * u) * star u
      = (u * star u) * a * (u * star u) := by noncomm_ring
    _ = a := by rw [Unitary.mul_star_self_of_mem hu, one_mul, mul_one]

/-- Conjugation by a unitary is an isometry of the dual. -/
theorem norm_conjFunctional {u : A} (hu : u ∈ unitary A) (f : A →L[ℂ] ℂ) :
    ‖conjFunctional hu f‖ = ‖f‖ := by
  refine le_antisymm (norm_conjFunctional_le hu f) ?_
  calc ‖f‖
      = ‖conjFunctional (Unitary.star_mem hu) (conjFunctional hu f)‖ := by
        rw [conjFunctional_conjFunctional]
    _ ≤ ‖conjFunctional hu f‖ := norm_conjFunctional_le _ _

theorem conjFunctional_sub {u : A} (hu : u ∈ unitary A) (f g : A →L[ℂ] ℂ) :
    conjFunctional hu (f - g) = conjFunctional hu f - conjFunctional hu g :=
  ContinuousLinearMap.ext fun _ ↦ rfl

/-- Conjugation by a unitary preserves positivity. -/
theorem IsPositiveFunctional.conj {u : A} (hu : u ∈ unitary A)
    {f : A →L[ℂ] ℂ} (hf : IsPositiveFunctional f) :
    IsPositiveFunctional (conjFunctional hu f) := by
  intro z
  rw [conjFunctional_apply]
  have hz : u * (star z * z) * star u = star (z * star u) * (z * star u) := by
    rw [star_mul, star_star]
    noncomm_ring
  rw [hz]
  exact hf _

/-- A tracial functional is fixed by every unitary conjugation. -/
theorem conjFunctional_eq_self_of_isTracial {u : A} (hu : u ∈ unitary A)
    {f : A →L[ℂ] ℂ} (hf : IsTracialFunctional f) :
    conjFunctional hu f = f := by
  refine ContinuousLinearMap.ext fun a ↦ ?_
  rw [conjFunctional_apply, hf (u * a) (star u)]
  congr 1
  rw [← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul]

/-- **Conversely**, a functional fixed by every unitary conjugation is
tracial.  This is where the unitaries have to span: the invariance gives
`f (u x) = f (x u)` for unitary `u`, and Mathlib's
`CStarAlgebra.exists_sum_four_unitary` upgrades that to all of `A`. -/
theorem isTracialFunctional_of_unitary_invariant {f : A →L[ℂ] ℂ}
    (h : ∀ u : A, u ∈ unitary A → ∀ a : A, f (u * a * star u) = f a) :
    IsTracialFunctional f := by
  have step : ∀ u : A, u ∈ unitary A → ∀ x : A, f (u * x) = f (x * u) := by
    intro u hu x
    have hx := h u hu (x * u)
    have hrw : u * (x * u) * star u = u * x := by
      calc u * (x * u) * star u = u * x * (u * star u) := by noncomm_ring
        _ = u * x := by rw [Unitary.mul_star_self_of_mem hu, mul_one]
    rwa [hrw] at hx
  intro a b
  obtain ⟨v, c, hb, -⟩ := CStarAlgebra.exists_sum_four_unitary b
  subst hb
  rw [Finset.mul_sum, Finset.sum_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, map_smul]
  congr 1
  exact (step (v i : A) (v i).2 a).symm

/-! ## The Jordan decomposition, as a named hypothesis -/

/-- **Existence of the norm-additive Jordan decomposition** of a bounded
hermitian functional on a unital C-star-algebra.  Cuntz--Pedersen, J. Funct.
Anal. 33 (1979); the underlying theorem is Takesaki, *Theory of Operator
Algebras I*, III.4.2.  Its standard proof passes through the enveloping von
Neumann algebra, which Mathlib does not yet have; the statement is therefore
carried as a hypothesis rather than an axiom. -/
def HasJordanDecomposition (C : Type u) [CStarAlgebra C] : Prop :=
  ∀ f : C →L[ℂ] ℂ, IsHermitianFunctional f →
    ∃ p q : C →L[ℂ] ℂ, IsPositiveFunctional p ∧ IsPositiveFunctional q ∧
      f = p - q ∧ ‖f‖ = ‖p‖ + ‖q‖

/-- **Uniqueness of the norm-additive Jordan decomposition.**  The
norm-additivity clause `‖p - q‖ = ‖p‖ + ‖q‖` is exactly minimality of the
pair, and it is what pins the decomposition down. -/
def HasUniqueJordanDecomposition (C : Type u) [CStarAlgebra C] : Prop :=
  ∀ p q p' q' : C →L[ℂ] ℂ, IsPositiveFunctional p → IsPositiveFunctional q →
    IsPositiveFunctional p' → IsPositiveFunctional q' →
    p - q = p' - q' → ‖p - q‖ = ‖p‖ + ‖q‖ → ‖p' - q'‖ = ‖p'‖ + ‖q'‖ →
    p = p' ∧ q = q'

/-- **The tracial refinement of the Jordan decomposition.**  If a hermitian
functional is tracial, then both parts of a norm-additive Jordan
decomposition are tracial.

The mechanism is invariance plus uniqueness: conjugating the pair `(p, q)` by
a unitary produces another norm-additive Jordan pair of the *same* functional,
because conjugation is an isometry of the dual, preserves positivity, and
fixes the tracial `f`.  Uniqueness then forces the pair to be fixed, and a
functional fixed by all unitary conjugations is tracial. -/
theorem isTracialFunctional_jordan_parts
    (huniq : HasUniqueJordanDecomposition A)
    {f p q : A →L[ℂ] ℂ} (hft : IsTracialFunctional f)
    (hp : IsPositiveFunctional p) (hq : IsPositiveFunctional q)
    (hpq : f = p - q) (hnorm : ‖f‖ = ‖p‖ + ‖q‖) :
    IsTracialFunctional p ∧ IsTracialFunctional q := by
  have hfix : ∀ (u : A) (hu : u ∈ unitary A),
      conjFunctional hu p = p ∧ conjFunctional hu q = q := by
    intro u hu
    have hsub : conjFunctional hu p - conjFunctional hu q = p - q := by
      rw [← conjFunctional_sub, ← hpq, conjFunctional_eq_self_of_isTracial hu hft]
    refine huniq _ _ _ _ (IsPositiveFunctional.conj hu hp)
      (IsPositiveFunctional.conj hu hq) hp hq hsub ?_ ?_
    · rw [hsub, norm_conjFunctional, norm_conjFunctional, ← hpq]
      exact hnorm
    · rw [← hpq]
      exact hnorm
  refine ⟨isTracialFunctional_of_unitary_invariant ?_,
    isTracialFunctional_of_unitary_invariant ?_⟩
  · intro u hu a
    have hval := DFunLike.congr_fun (hfix u hu).1 a
    rwa [conjFunctional_apply] at hval
  · intro u hu a
    have hval := DFunLike.congr_fun (hfix u hu).2 a
    rwa [conjFunctional_apply] at hval

/-- Cuntz--Pedersen's decomposition for a bounded hermitian **tracial**
functional: both parts are positive *and* tracial. -/
theorem exists_positive_tracial_jordan
    (hJ : HasJordanDecomposition A) (huniq : HasUniqueJordanDecomposition A)
    {f : A →L[ℂ] ℂ} (hfh : IsHermitianFunctional f)
    (hft : IsTracialFunctional f) :
    ∃ p q : A →L[ℂ] ℂ, IsPositiveFunctional p ∧ IsPositiveFunctional q ∧
      IsTracialFunctional p ∧ IsTracialFunctional q ∧
      f = p - q ∧ ‖f‖ = ‖p‖ + ‖q‖ := by
  obtain ⟨p, q, hp, hq, hpq, hnorm⟩ := hJ f hfh
  obtain ⟨hpt, hqt⟩ :=
    isTracialFunctional_jordan_parts huniq hft hp hq hpq hnorm
  exact ⟨p, q, hp, hq, hpt, hqt, hpq, hnorm⟩

/-! ## Normalization to a tracial state -/

/-- Normalize a positive tracial functional which does not kill the unit. -/
def normalizedTracialState {p : A →L[ℂ] ℂ} (hp : IsPositiveFunctional p)
    (htr : IsTracialFunctional p) (h1 : p 1 ≠ 0) : TracialState A where
  toLinearMap := (p 1)⁻¹ • p.toLinearMap
  map_one := by
    show (p 1)⁻¹ • p 1 = 1
    rw [smul_eq_mul, inv_mul_cancel₀ h1]
  map_star_mul_self_nonneg x := by
    show (0 : ℂ) ≤ (p 1)⁻¹ • p (star x * x)
    rw [smul_eq_mul]
    exact mul_nonneg_complex (inv_nonneg_complex hp.apply_one_nonneg) (hp x)
  map_mul_comm x y := by
    show (p 1)⁻¹ • p (x * y) = (p 1)⁻¹ • p (y * x)
    rw [htr x y]

@[simp] theorem normalizedTracialState_apply {p : A →L[ℂ] ℂ}
    (hp : IsPositiveFunctional p) (htr : IsTracialFunctional p) (h1 : p 1 ≠ 0)
    (a : A) : normalizedTracialState hp htr h1 a = (p 1)⁻¹ * p a := rfl

/-- A positive tracial functional detecting `x` yields a tracial state
detecting `x`.  Nondegeneracy at the unit is not an extra hypothesis: it
follows from `IsPositiveFunctional.eq_zero_of_apply_one_eq_zero`. -/
theorem exists_tracialState_of_positive_tracial {p : A →L[ℂ] ℂ}
    (hp : IsPositiveFunctional p) (htr : IsTracialFunctional p)
    {x : A} (hx : p x ≠ 0) : ∃ τ : TracialState A, τ x ≠ 0 := by
  have h1 : p 1 ≠ 0 := fun h ↦ hx (hp.eq_zero_of_apply_one_eq_zero h x)
  refine ⟨normalizedTracialState hp htr h1, ?_⟩
  rw [normalizedTracialState_apply]
  exact mul_ne_zero (inv_ne_zero h1) hx

/-! ## Cuntz--Pedersen separation -/

/-- **Cuntz--Pedersen separation follows from the Jordan decomposition.**
This discharges the hypothesis `HasCuntzPedersenSeparation` used by
`CuntzPedersenCoronaObstruction` against the two standard Jordan
statements. -/
theorem hasCuntzPedersenSeparation_of_jordan
    (hJ : HasJordanDecomposition A) (huniq : HasUniqueJordanDecomposition A) :
    HasCuntzPedersenSeparation A := by
  intro x hxstar hx
  obtain ⟨φ, hφx, -⟩ := exists_hermitianTrace_detecting hxstar hx
  have hfx : φ.toContinuousLinearMap x ≠ 0 := hφx
  obtain ⟨p, q, hp, hq, hpt, hqt, hfpq, -⟩ :=
    exists_positive_tracial_jordan (f := φ.toContinuousLinearMap) hJ huniq
      (fun a ↦ φ.map_star' a) (fun a b ↦ φ.map_mul_comm' a b)
  have hsub : φ.toContinuousLinearMap x = p x - q x := by
    rw [hfpq]
    rfl
  by_cases hpx : p x = 0
  · refine exists_tracialState_of_positive_tracial hq hqt (x := x) ?_
    intro hqx
    exact hfx (by rw [hsub, hpx, hqx, sub_zero])
  · exact exists_tracialState_of_positive_tracial hp hpt hpx

/-! ## Consequence for the norm corona -/

section Corona

open Filter

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)] [∀ n, Nontrivial (D n)]

/-- The obstructing corona class of a `BlockObstruction` is detected by a
genuine tracial state as soon as the corona has a Jordan decomposition.  This
is the exact form of the step used in Section 6 of the Problem XXII
counterexample audit: the Chern-class obstruction puts the class outside the
trace-zero space, Hahn--Banach produces a signed trace, and the Jordan
decomposition turns that into a positive tracial one. -/
theorem exists_tracialState_detecting_coronaClass_of_jordan
    (B : BlockObstruction D)
    (hJ : HasJordanDecomposition (CStarProductCorona D atTop))
    (huniq : HasUniqueJordanDecomposition (CStarProductCorona D atTop)) :
    ∃ τ : TracialState (CStarProductCorona D atTop), τ B.coronaClass ≠ 0 :=
  exists_tracialState_detecting_coronaClass B
    (hasCuntzPedersenSeparation_of_jordan hJ huniq)

end Corona

end

end CuntzPedersenJordanTracial
end GroupApproximation
