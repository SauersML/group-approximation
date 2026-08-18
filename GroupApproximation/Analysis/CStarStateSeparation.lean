import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# States separate the points of a unital C⋆-algebra

## What this module proves

For a unital C⋆-algebra `A` and any `a : A` there is a **norm-attaining
state**: a continuous linear functional `f : A →L[ℂ] ℂ` with `f 1 = 1`,
`‖f‖ ≤ 1`, and

  `f (star a * a) = ‖a‖²`.

This is the analytic engine behind every canonical construction the tensor
lane still lacks: it is what makes the family of GNS representations
*jointly faithful and isometric*, hence what lets a supremum over a set-sized
family of state-derived representations stand in for "all representations".
Stage C of the roadmap in `CStarTensorProduct.lean` begins here.

## The design decision: states without an order structure

Mathlib's `A →ₚ[ℂ] ℂ` positive maps require `[PartialOrder A]` and
`[StarOrderedRing A]` side instances.  The concrete algebras of this
repository -- closed `StarSubalgebra`s of `B(ℓ²G)` and completions built
through `WithCStarNorm` -- do not carry them, and `CStarExactness.lean`
already respells complete positivity in the order-free form `∃ N, M = star N
* N` for exactly this reason.  This module does the same for states: a state
is a **unital contraction** `f 1 = 1 ∧ ‖f‖ ≤ 1`, and its positivity is a
*theorem* (`im_apply_eq_zero_of_isSelfAdjoint`, `re_apply_nonneg_of_spectrum_nonneg`)
rather than a definition.  By Kadison's classical characterization the two
notions agree; here the unital-contraction side is taken as primitive because
it needs no order instance to state.

## The route

Everything runs through the spectrum, with no Gelfand duality and no
characters:

1. For selfadjoint `x` and real `t`, the C⋆-identity gives
   `‖x + it‖² ≤ ‖x‖² + t²`; letting `t → ±∞` forces `(f x).im = 0` for any
   unital contraction `f`.  (`im_apply_eq_zero_of_isSelfAdjoint`)
2. For any `μ ∈ spectrum ℂ y` there is a unital contraction with `f y = μ`:
   define `s•1 + t•y ↦ s + tμ` on the span of `{1, y}` -- bounded because
   `s + tμ` lies in `spectrum ℂ (s•1 + t•y)` and spectral values are norm
   bounds -- and extend by Hahn--Banach.
   (`exists_unitalContraction_apply_eq`)
3. `‖b‖ ∈ spectrum ℂ b` for `b = star a * a`: the spectral radius of a
   selfadjoint element is its norm and is attained, the attaining value is
   real, and `spectrum_star_mul_self_nonneg` rules out `-‖b‖`.
   (`norm_mem_spectrum_star_mul_self`)
4. Combining 2 and 3 yields the norm-attaining state.
   (`exists_state_star_mul_self`)
5. For a unital contraction, `(f y).re ≥ 0` whenever `y` is selfadjoint with
   nonnegative spectrum -- Kadison's positivity, order-free.
   (`re_apply_nonneg_of_spectrum_nonneg`, `state_apply_star_mul_self_nonneg`)

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.  This module is Stage C.1 of the tensor-lane
roadmap: the statehood needed for a canonical minimal tensor norm.  The GNS
representations off these states, the supremum norm over state pairs, and the
identification with the spatial norm of a faithful pair (Takesaki) are not
here.
-/

namespace GroupApproximation
namespace CStarState

open scoped ComplexOrder Pointwise

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-! ## The C⋆-identity bound for a selfadjoint element shifted by `it` -/

/-- For selfadjoint `x` and real `t`, the C⋆-identity gives
`‖x + it‖² ≤ ‖x‖² + t²`: the cross terms of `(x - it)(x + it)` cancel because
`it` is central. -/
theorem norm_sq_add_smul_I_le {x : A} (hx : IsSelfAdjoint x) (t : ℝ) :
    ‖x + ((t : ℂ) * Complex.I) • (1 : A)‖ ^ 2 ≤ ‖x‖ ^ 2 + t ^ 2 := by
  set c : ℂ := (t : ℂ) * Complex.I with hc
  have hstarc : star c = -c := by
    simp [hc, Complex.conj_ofReal, mul_comm]
  have hstar : star (x + c • (1 : A)) = x - c • (1 : A) := by
    rw [star_add, hx.star_eq, star_smul, star_one, hstarc, neg_smul,
      ← sub_eq_add_neg]
  have h1 : (c • (1 : A)) * x = c • x := by rw [smul_mul_assoc, one_mul]
  have h2 : x * (c • (1 : A)) = c • x := by rw [mul_smul_comm, mul_one]
  have h3 : (c • (1 : A)) * (c • (1 : A)) = (c * c) • (1 : A) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
  have hcc : c * c = -((t : ℂ) ^ 2) := by
    rw [hc]
    ring_nf
    simp [Complex.I_sq]
  have hmul : star (x + c • (1 : A)) * (x + c • (1 : A))
      = x * x + ((t : ℂ) ^ 2) • (1 : A) := by
    have hmul' : star (x + c • (1 : A)) * (x + c • (1 : A))
        = x * x - (c * c) • (1 : A) := by
      rw [hstar, sub_mul, mul_add, mul_add, h1, h2, h3]
      abel
    rw [hmul', hcc, neg_smul, sub_neg_eq_add]
  have hnorm : ‖x + c • (1 : A)‖ ^ 2
      = ‖star (x + c • (1 : A)) * (x + c • (1 : A))‖ := by
    rw [CStarRing.norm_star_mul_self, sq]
  have hsmul : ‖((t : ℂ) ^ 2) • (1 : A)‖ = t ^ 2 := by
    rw [norm_smul, norm_one, mul_one]
    have hcast : ((t : ℂ) ^ 2) = (((t ^ 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg t)]
  calc ‖x + c • (1 : A)‖ ^ 2
      = ‖star (x + c • (1 : A)) * (x + c • (1 : A))‖ := hnorm
    _ = ‖x * x + ((t : ℂ) ^ 2) • (1 : A)‖ := by rw [hmul]
    _ ≤ ‖x * x‖ + ‖((t : ℂ) ^ 2) • (1 : A)‖ := norm_add_le _ _
    _ ≤ ‖x‖ * ‖x‖ + t ^ 2 := by
        gcongr
        · exact norm_mul_le x x
        · rw [hsmul]
    _ = ‖x‖ ^ 2 + t ^ 2 := by ring

/-! ## Unital contractions are real on selfadjoint elements -/

/-- **A unital contraction takes real values on selfadjoint elements.**  The
half of positivity that needs nothing about the spectrum: if `(f x).im ≠ 0`,
then `|(f x).im + t| ≤ ‖x + it‖ ≤ √(‖x‖² + t²)` fails for a suitable real
`t`. -/
theorem im_apply_eq_zero_of_isSelfAdjoint (f : A →L[ℂ] ℂ) (hf1 : f 1 = 1)
    (hf : ‖f‖ ≤ 1) {x : A} (hx : IsSelfAdjoint x) : (f x).im = 0 := by
  have key : ∀ t : ℝ, ((f x).im + t) ^ 2 ≤ ‖x‖ ^ 2 + t ^ 2 := by
    intro t
    have hz := norm_sq_add_smul_I_le hx t
    set z : A := x + ((t : ℂ) * Complex.I) • (1 : A) with hzdef
    have hfz : f z = f x + (t : ℂ) * Complex.I := by
      rw [hzdef, map_add, map_smul, hf1, smul_eq_mul, mul_one]
    have him : (f z).im = (f x).im + t := by
      rw [hfz]
      simp
    have h1 : |(f z).im| ≤ ‖f z‖ := Complex.abs_im_le_norm _
    have h2 : ‖f z‖ ≤ ‖z‖ := by
      calc ‖f z‖ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
        _ ≤ 1 * ‖z‖ := by gcongr
        _ = ‖z‖ := one_mul _
    have h3 : ((f x).im + t) ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← him]
      calc (f z).im ^ 2 = |(f z).im| ^ 2 := (sq_abs _).symm
        _ ≤ ‖f z‖ ^ 2 := by gcongr
        _ ≤ ‖z‖ ^ 2 := by gcongr
    exact h3.trans hz
  by_contra him
  have hkey : ∀ t : ℝ, (f x).im ^ 2 + 2 * (f x).im * t ≤ ‖x‖ ^ 2 := by
    intro t
    have := key t
    nlinarith [this]
  have := hkey (‖x‖ ^ 2 / (2 * (f x).im))
  have h2im : 2 * (f x).im ≠ 0 := by
    intro h
    exact him (by linarith [mul_eq_zero.mp h |>.resolve_left two_ne_zero])
  rw [mul_div_cancel₀ _ h2im] at this
  have him2 : 0 < (f x).im ^ 2 := by positivity
  linarith

/-! ## Spectral values are attained by unital contractions -/

/-- Membership of an affine image in the spectrum of an affine combination:
if `μ ∈ spectrum ℂ y` then `s + t·μ ∈ spectrum ℂ (s•1 + t•y)`. -/
theorem affine_mem_spectrum {y : A} {μ : ℂ} (hμ : μ ∈ spectrum ℂ y)
    (s t : ℂ) : s + t * μ ∈ spectrum ℂ (s • (1 : A) + t • y) := by
  have halg : ∀ r : ℂ, r • (1 : A) = algebraMap ℂ A r := fun r =>
    (Algebra.algebraMap_eq_smul_one r).symm
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [zero_mul, add_zero, zero_smul]
    have h0 : spectrum ℂ (0 : A) = {0} := spectrum.zero_eq (𝕜 := ℂ)
    have := spectrum.singleton_add_eq (0 : A) s
    rw [h0] at this
    have hmem : s ∈ ({s} + ({0} : Set ℂ)) := by
      have h := Set.add_mem_add (Set.mem_singleton s)
        (Set.mem_singleton (0 : ℂ))
      rwa [add_zero] at h
    rw [this] at hmem
    rwa [add_zero, ← halg] at hmem
  · have hsmul : spectrum ℂ (t • y) = t • spectrum ℂ y := by
      have hne : (spectrum ℂ y).Nonempty := ⟨μ, hμ⟩
      exact spectrum.smul_eq_smul t y hne
    have hmem : t * μ ∈ spectrum ℂ (t • y) := by
      rw [hsmul]
      exact ⟨μ, hμ, rfl⟩
    have := spectrum.singleton_add_eq (t • y) s
    have hmem2 : s + t * μ ∈ ({s} + spectrum ℂ (t • y)) :=
      Set.add_mem_add (Set.mem_singleton s) hmem
    rw [this] at hmem2
    rwa [← halg] at hmem2

/-- **Every spectral value is the value of a unital contraction.**  The span
of `{1, y}` carries the functional `s•1 + t•y ↦ s + tμ`, bounded by `1`
because affine combinations of spectral values are spectral values and
spectral values bound no norm from above; Hahn--Banach extends it. -/
theorem exists_unitalContraction_apply_eq (y : A) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ y) :
    ∃ f : A →L[ℂ] ℂ, f 1 = 1 ∧ ‖f‖ ≤ 1 ∧ f y = μ := by
  classical
  by_cases hdep : ∃ c : ℂ, y = c • (1 : A)
  · -- Degenerate case: `y` is a scalar, so `μ` is that scalar and any
    -- unital contraction works; one exists by `exists_dual_vector` at `1`.
    obtain ⟨c, rfl⟩ := hdep
    have hμc : μ = c := by
      have h0 : spectrum ℂ (0 : A) = {0} := spectrum.zero_eq (𝕜 := ℂ)
      have hsing := spectrum.singleton_add_eq (0 : A) c
      rw [h0] at hsing
      have : spectrum ℂ (c • (1 : A)) = {c} + ({0} : Set ℂ) := by
        rw [hsing, add_zero, Algebra.algebraMap_eq_smul_one]
      rw [this] at hμ
      simpa using hμ
    have hone : ‖(1 : A)‖ ≠ 0 := by
      rw [norm_one]; exact one_ne_zero
    obtain ⟨g, hg1, hgx⟩ := exists_dual_vector ℂ (1 : A) hone
    refine ⟨g, ?_, le_of_eq hg1, ?_⟩
    · rw [hgx, norm_one, RCLike.ofReal_one]
    · rw [map_smul, smul_eq_mul, hgx, norm_one, RCLike.ofReal_one, mul_one,
        hμc]
  · -- Independent case: `{y, 1}` is linearly independent, so the pinned
    -- functional is well defined on the span and bounded by the affine
    -- spectral-membership lemma.
    rw [not_exists] at hdep
    have hli : LinearIndependent ℂ ![y, (1 : A)] := by
      rw [linearIndependent_fin2]
      refine ⟨by simp, fun c => ?_⟩
      exact fun h => hdep c h.symm
    set p : Submodule ℂ A := Submodule.span ℂ (Set.range ![y, (1 : A)])
      with hp
    haveI : FiniteDimensional ℂ p :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    set B : Module.Basis (Fin 2) ℂ p := Module.Basis.span hli with hB
    set f₀ : p →ₗ[ℂ] ℂ := B.constr ℕ ![μ, 1] with hf₀
    have hB0 : (B 0 : A) = y :=
      congrArg Subtype.val (Module.Basis.span_apply hli 0)
    have hB1 : (B 1 : A) = (1 : A) :=
      congrArg Subtype.val (Module.Basis.span_apply hli 1)
    have hval : ∀ (s t : ℂ) (v : p), (v : A) = t • y + s • (1 : A) →
        f₀ v = t * μ + s := by
      intro s t v hv
      have hvB : v = t • B 0 + s • B 1 := by
        apply Subtype.ext
        push_cast
        rw [hB0, hB1]
        exact hv
      rw [hvB, map_add, map_smul, map_smul, hf₀, Module.Basis.constr_basis,
        Module.Basis.constr_basis]
      simp [smul_eq_mul]
    have hbound : ∀ v : p, ‖f₀ v‖ ≤ ‖v‖ := by
      intro v
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp v.2
      have hcv : (v : A) = c 0 • y + c 1 • (1 : A) := by
        rw [← hc, Fin.sum_univ_two]
        simp
      have hfv : f₀ v = c 0 * μ + c 1 := by
        have := hval (c 1) (c 0) v hcv
        simpa using this
      have hmem : c 1 + c 0 * μ ∈ spectrum ℂ (c 1 • (1 : A) + c 0 • y) :=
        affine_mem_spectrum hμ (c 1) (c 0)
      have hnorm : ‖c 1 + c 0 * μ‖ ≤ ‖c 1 • (1 : A) + c 0 • y‖ :=
        spectrum.norm_le_norm_of_mem hmem
      calc ‖f₀ v‖ = ‖c 1 + c 0 * μ‖ := by rw [hfv, add_comm]
        _ ≤ ‖c 1 • (1 : A) + c 0 • y‖ := hnorm
        _ = ‖(v : A)‖ := by rw [hcv, add_comm]
        _ = ‖v‖ := rfl
    set F₀ : p →L[ℂ] ℂ := LinearMap.toContinuousLinearMap f₀ with hF₀
    have hF₀le : ‖F₀‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      rw [one_mul]
      exact hbound v
    obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq p F₀
    have h1mem : (1 : A) ∈ p := by
      apply Submodule.subset_span
      exact ⟨1, by simp⟩
    have hymem : y ∈ p := by
      apply Submodule.subset_span
      exact ⟨0, by simp⟩
    refine ⟨g, ?_, ?_, ?_⟩
    · rw [hg ⟨1, h1mem⟩]
      show f₀ ⟨1, h1mem⟩ = 1
      have h := hval 1 0 ⟨1, h1mem⟩ (by simp)
      simpa using h
    · rw [hgnorm]
      exact hF₀le
    · rw [hg ⟨y, hymem⟩]
      show f₀ ⟨y, hymem⟩ = μ
      have h := hval 0 1 ⟨y, hymem⟩ (by simp)
      simpa using h

/-! ## The norm of `star a * a` is in its spectrum -/

/-- For `b = star a * a` the norm is a spectral value: the spectral radius of
a selfadjoint element is its norm and is attained, the attaining value is
real, and nonnegativity of the spectrum of `star a * a` fixes its sign. -/
theorem norm_mem_spectrum_star_mul_self (a : A) :
    ((‖star a * a‖ : ℝ) : ℂ) ∈ spectrum ℂ (star a * a) := by
  set b : A := star a * a with hb
  have hsa : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self a
  obtain ⟨z, hz, hznorm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
      (spectrum.nonempty b)
  have hzre : z = z.re := hsa.mem_spectrum_eq_re hz
  have hre_mem : (z.re : ℝ) ∈ spectrum ℝ b := by
    apply spectrum.of_algebraMap_mem ℂ
    show ((z.re : ℝ) : ℂ) ∈ spectrum ℂ b
    rw [← hzre]
    exact hz
  have hre_nonneg : 0 ≤ z.re := spectrum_star_mul_self_nonneg z.re hre_mem
  have hznorm' : ‖z‖ = ‖b‖ := by
    have := hsa.spectralRadius_eq_nnnorm
    rw [this] at hznorm
    have h : ‖z‖₊ = ‖b‖₊ := by exact_mod_cast hznorm
    exact congrArg NNReal.toReal h
  have hzval : z.re = ‖b‖ := by
    have : ‖z‖ = |z.re| := by
      conv_lhs => rw [hzre]
      exact Complex.norm_real z.re
    rw [this, abs_of_nonneg hre_nonneg] at hznorm'
    exact hznorm'
  have : z = ((‖b‖ : ℝ) : ℂ) := by
    rw [hzre, hzval]
  rwa [this] at hz

/-! ## The norm-attaining state -/

/-- **States separate points, quantitatively**: for every `a` there is a
unital contraction `f` with `f (star a * a) = ‖a‖²`.  This is the statement
that makes the family of GNS representations of states jointly isometric,
and with it every canonical construction over "all representations" can be
carried by the set-sized family of states. -/
theorem exists_state_star_mul_self (a : A) :
    ∃ f : A →L[ℂ] ℂ, f 1 = 1 ∧ ‖f‖ ≤ 1 ∧
      f (star a * a) = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
  obtain ⟨f, hf1, hfnorm, hfval⟩ :=
    exists_unitalContraction_apply_eq (star a * a)
      (norm_mem_spectrum_star_mul_self a)
  refine ⟨f, hf1, hfnorm, ?_⟩
  rw [hfval, CStarRing.norm_star_mul_self]
  push_cast
  ring

/-! ## Kadison positivity, order-free -/

/-- A unital contraction is nonnegative on selfadjoint elements with
nonnegative real spectrum: `‖y - ‖y‖·1‖ ≤ ‖y‖` because the shifted spectrum
lies in `[-‖y‖, 0]`, so `|f y - ‖y‖| ≤ ‖y‖` and the real part of `f y` is
nonnegative. -/
theorem re_apply_nonneg_of_spectrum_nonneg (f : A →L[ℂ] ℂ) (hf1 : f 1 = 1)
    (hf : ‖f‖ ≤ 1) {y : A} (hy : IsSelfAdjoint y)
    (hspec : ∀ s ∈ spectrum ℝ y, 0 ≤ s) : 0 ≤ (f y).re := by
  set r : ℝ := ‖y‖ with hr
  set w : A := y - ((r : ℂ)) • (1 : A) with hw
  have hwsa : IsSelfAdjoint w := by
    rw [hw]
    refine hy.sub ?_
    have : IsSelfAdjoint ((r : ℂ) • (1 : A)) := by
      rw [IsSelfAdjoint, star_smul, star_one, Complex.star_def,
        Complex.conj_ofReal]
    exact this
  -- Every spectral value of `w` has modulus at most `r`.
  have hwspec : ∀ z ∈ spectrum ℂ w, ‖z‖ ≤ r := by
    intro z hz
    have hshift : spectrum ℂ w = spectrum ℂ y - ({(r : ℂ)} : Set ℂ) := by
      rw [hw, ← Algebra.algebraMap_eq_smul_one (R := ℂ) (A := A) (r : ℂ)]
      exact (spectrum.sub_singleton_eq y (r : ℂ)).symm
    rw [hshift] at hz
    obtain ⟨u, hu, v, hv, huv⟩ := hz
    rw [Set.mem_singleton_iff] at hv
    subst hv
    have hure : u = u.re := hy.mem_spectrum_eq_re hu
    have hurange : 0 ≤ u.re ∧ u.re ≤ r := by
      constructor
      · refine hspec u.re ?_
        apply spectrum.of_algebraMap_mem ℂ
        show ((u.re : ℝ) : ℂ) ∈ spectrum ℂ y
        rw [← hure]; exact hu
      · have := spectrum.norm_le_norm_of_mem hu
        rw [hure, Complex.norm_real] at this
        exact (abs_le.mp (this.trans_eq rfl)).2
    rw [← huv, hure]
    show ‖((u.re : ℂ)) - ((r : ℂ))‖ ≤ r
    have : ((u.re : ℂ)) - ((r : ℂ)) = (((u.re - r : ℝ)) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> [linarith [hurange.2]; linarith [hurange.1, norm_nonneg y]]
  -- Hence `‖w‖ ≤ r`, by attainment of the spectral radius.
  have hwnorm : ‖w‖ ≤ r := by
    obtain ⟨z, hz, hznorm⟩ :=
      spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
        (spectrum.nonempty w)
    have := hwsa.spectralRadius_eq_nnnorm
    rw [this] at hznorm
    have hzw : ‖z‖ = ‖w‖ := by
      have h : ‖z‖₊ = ‖w‖₊ := by exact_mod_cast hznorm
      exact congrArg NNReal.toReal h
    rw [← hzw]
    exact hwspec z hz
  -- Push through `f` and take real parts.
  have hfw : f w = f y - (r : ℂ) := by
    rw [hw, map_sub, map_smul, hf1, smul_eq_mul, mul_one]
  have hbound : ‖f w‖ ≤ r := by
    calc ‖f w‖ ≤ ‖f‖ * ‖w‖ := f.le_opNorm w
      _ ≤ 1 * r := by
          have h0r : (0:ℝ) ≤ r := norm_nonneg y
          exact mul_le_mul hf hwnorm (norm_nonneg w) zero_le_one
      _ = r := one_mul r
  have hre : |(f w).re| ≤ r := (Complex.abs_re_le_norm _).trans hbound
  have hwre : (f w).re = (f y).re - r := by
    rw [hfw]
    simp
  rw [hwre, abs_le] at hre
  linarith [hre.1]

/-- **A unital contraction is a state**: it is nonnegative on every element
of the form `star x * x`, with real value.  Positivity in the order-free
spelling of this repository. -/
theorem state_apply_star_mul_self_nonneg (f : A →L[ℂ] ℂ) (hf1 : f 1 = 1)
    (hf : ‖f‖ ≤ 1) (x : A) :
    0 ≤ (f (star x * x)).re ∧ (f (star x * x)).im = 0 := by
  refine ⟨?_, ?_⟩
  · exact re_apply_nonneg_of_spectrum_nonneg f hf1 hf
      (IsSelfAdjoint.star_mul_self x)
      (spectrum_star_mul_self_nonneg)
  · exact im_apply_eq_zero_of_isSelfAdjoint f hf1 hf
      (IsSelfAdjoint.star_mul_self x)

end CStarState
end GroupApproximation
