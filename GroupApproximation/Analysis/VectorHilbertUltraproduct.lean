import GroupApproximation.Sofic.FrobeniusPairing
import GroupApproximation.Sofic.MarkedCompressionVectorChain
import GroupApproximation.Sofic.UltrafilterLimit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `H_ω`, the Hilbert-space ultraproduct of the coordinate spaces `ℂ^{d_n}`

The printed proof of `\label{thm:normal-kazhdan}` opens its Kazhdan-corner
paragraph with

> Fix a free ultrafilter `ω`, let `H_ω` be the Hilbert-space ultraproduct of the
> coordinate spaces `ℂ^{d_n}`, and let `B_ω = ∏_ω B(ℂ^{d_n})` act on it as in
> Section~\ref{sec:transport}, so that the classes `π(g) = [V_{g,n}]_ω` define a
> unitary representation of `H̄` on `H_ω`.

This is **not** the ultraproduct the development already has.
`Sofic/UltraproductModelConstruction.lean` builds `K_ω`, the ultraproduct of the
*matrix* spaces `M_{d_n}(ℂ)` with the renormalized Hilbert--Schmidt inner
product, and its ambient algebra is the corona on the **doubled** index, because
`B(K_n)` is `M_{d_n²}`.  The normal-Kazhdan proof needs the ultraproduct of the
`ℂ^{d_n}` themselves, whose ambient is the corona on the undoubled index,
`∏_ω M_{d_n}`.  That gap is the single blocker behind the three open
normal-Kazhdan rows: `NK.05`'s printed ambient, `NK.06`'s `ran P = Fix π(K̄)`,
and `NK.07`'s lift of `q` to coordinate projections.

This file builds `H_ω` and gives it its inner product.

## The construction, and where it is simpler than `K_ω`

Bounded families of vectors modulo families null along `ω`:

`H_ω = {ξ : ∀ n, ℂ^{d_n} | sup_n ‖ξ_n‖ < ∞} / {ξ | lim_ω ‖ξ_n‖ = 0}`,

with `⟨[ξ], [η]⟩ = lim_ω ∑_i conj(ξ_n i) · η_n i`.

Two simplifications over the matrix construction.

*No weight.*  The printed vector spaces carry none -- the renormalization in
`thm:normal-kazhdan` is of the *trace* on the corner, not of the coordinate
Hilbert spaces -- so `vecBounded` and `vecNull` need no clipped weight and none
of the `w n = 0` case analysis `massBounded` and `massNull` carry.

*Cauchy--Schwarz is available.*  `Sofic/HilbertUltraproductInner.lean` had to
replace it by a rescaled arithmetic--geometric bound, because the development
carries no inner product on matrices.  Here the coordinate space **is**
`EuclideanSpace ℂ (Y n)` on the nose, so `norm_inner_le_norm` applies directly
and the step that a null family pairs to zero against a bounded one becomes a
product of a vanishing factor with a bounded one.

The mass `vecMass` and its submodule estimates are reused verbatim from
`Sofic/MarkedCompressionVectorChain.lean`.

## What follows this file

Completeness of `H_ω`, by the argument of `Analysis/OmegaHilbertComplete.lean` --
the absolutely-convergent-series criterion, a truncation lemma producing
representatives bounded at *every* stage, and coordinatewise summation -- and
then the action of `∏_ω M_{d_n}` on `H_ω` with its faithfulness.  `evec_sum` is
already here because the summation step is what consumes it; here the
coordinate space is `EuclideanSpace ℂ (Y n)` on the nose, so that argument
loses the vectorization the matrix case had to insert and undo.
-/

namespace GroupApproximation
namespace VectorHilbertUltraproduct

open Filter Topology
open MarkedCompressionVectorChain UltrafilterLimit

noncomputable section

/-! ## Coordinate vectors as elements of `ℓ²` -/

section Coordinates

variable {Z : FiniteModel}

/-- A coordinate vector, read in `ℓ²(Z)`. -/
def evec (x : Z → ℂ) : EuclideanSpace ℂ Z := WithLp.toLp 2 x

@[simp] theorem evec_apply (x : Z → ℂ) (i : Z) : evec x i = x i := rfl

theorem vecMass_eq_norm_sq (x : Z → ℂ) : vecMass x = ‖evec x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold vecMass
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [evec_apply]
  exact FrobeniusPairing.normSq_eq_norm_sq (x i)

theorem norm_evec (x : Z → ℂ) : ‖evec x‖ = Real.sqrt (vecMass x) := by
  rw [vecMass_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

@[simp] theorem evec_add (x y : Z → ℂ) : evec (x + y) = evec x + evec y := rfl

theorem evec_sum {ι : Type*} (s : Finset ι) (f : ι → Z → ℂ) :
    evec (∑ i ∈ s, f i) = ∑ i ∈ s, evec (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, evec_add, ih]

/-- The coordinate inner product, as mathlib's on `ℓ²(Z)`.  Conjugate-linear in
the first argument, which is the manuscript's convention too. -/
theorem inner_evec (x y : Z → ℂ) :
    inner ℂ (evec x) (evec y) = ∑ i : Z, (starRingEnd ℂ) (x i) * y i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact RCLike.inner_apply' (x i) (y i)

end Coordinates

/-! ## Families of coordinate vectors, and the coordinate pairing -/

section Pairing

variable {Y : ℕ → FiniteModel}

/-- A family of coordinate vectors, one in each `ℂ^{d_n}`. -/
abbrev VecFam (Y : ℕ → FiniteModel) : Type := ∀ n, (Y n) → ℂ

/-- The coordinate inner product of `ℂ^{d_n}`. -/
def vpairAt (ξ η : VecFam Y) (n : ℕ) : ℂ :=
  inner ℂ (evec (ξ n)) (evec (η n))

theorem vpairAt_eq_sum (ξ η : VecFam Y) (n : ℕ) :
    vpairAt ξ η n = ∑ i : Y n, (starRingEnd ℂ) (ξ n i) * η n i :=
  inner_evec (ξ n) (η n)

theorem vecMass_smul (Z : FiniteModel) (c : ℂ) (x : Z → ℂ) :
    vecMass (c • x) = Complex.normSq c * vecMass x := by
  unfold vecMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  show Complex.normSq (c * x i) = _
  rw [Complex.normSq_mul]

theorem vpairAt_self (ξ : VecFam Y) (n : ℕ) :
    vpairAt ξ ξ n = ((vecMass (ξ n) : ℝ) : ℂ) := by
  rw [vpairAt_eq_sum]
  unfold vecMass
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, Complex.mul_conj]

theorem vpairAt_conj (ξ η : VecFam Y) (n : ℕ) :
    (starRingEnd ℂ) (vpairAt ξ η n) = vpairAt η ξ n :=
  inner_conj_symm (evec (η n)) (evec (ξ n))

theorem vpairAt_add_right (ξ η ζ : VecFam Y) (n : ℕ) :
    vpairAt ξ (fun m ↦ η m + ζ m) n = vpairAt ξ η n + vpairAt ξ ζ n := by
  show inner ℂ (evec (ξ n)) (evec (η n + ζ n)) = _
  rw [evec_add, inner_add_right]
  rfl

theorem vpairAt_smul_right (c : ℂ) (ξ η : VecFam Y) (n : ℕ) :
    vpairAt ξ (fun m ↦ c • η m) n = c * vpairAt ξ η n := by
  show inner ℂ (evec (ξ n)) (evec (c • η n)) = _
  have hsmul : evec (c • η n) = c • evec (η n) := rfl
  rw [hsmul, inner_smul_right]
  rfl

/-- **Cauchy--Schwarz at a stage.**  Available because the coordinate space is
`ℓ²(Y n)` itself; the matrix construction had to substitute a rescaled
arithmetic--geometric bound for this. -/
theorem norm_vpairAt_le (ξ η : VecFam Y) (n : ℕ) :
    ‖vpairAt ξ η n‖
      ≤ Real.sqrt (vecMass (ξ n)) * Real.sqrt (vecMass (η n)) := by
  rw [← norm_evec, ← norm_evec]
  exact norm_inner_le_norm (evec (ξ n)) (evec (η n))

end Pairing

/-! ## `H_ω` as a module -/

section Space

variable (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ)

/-- **The numerator of `H_ω`**: families of coordinate vectors of bounded
Euclidean mass. -/
def vecBounded : Submodule ℂ (VecFam Y) where
  carrier := {ξ | ∃ C : ℝ, ∀ n, vecMass (ξ n) ≤ C}
  zero_mem' := by
    refine ⟨0, fun n ↦ ?_⟩
    show vecMass (0 : (Y n) → ℂ) ≤ 0
    unfold vecMass
    simp
  add_mem' := by
    rintro a b ⟨Ca, hA⟩ ⟨Cb, hB⟩
    refine ⟨2 * Ca + 2 * Cb, fun n ↦ ?_⟩
    show vecMass (a n + b n) ≤ 2 * Ca + 2 * Cb
    have h1 : vecMass (a n + b n) ≤ 2 * vecMass (a n) + 2 * vecMass (b n) :=
      vecMass_add_le _ _
    linarith [hA n, hB n]
  smul_mem' := by
    rintro c a ⟨Ca, hA⟩
    refine ⟨Complex.normSq c * Ca, fun n ↦ ?_⟩
    show vecMass (c • a n) ≤ Complex.normSq c * Ca
    rw [vecMass_smul]
    exact mul_le_mul_of_nonneg_left (hA n) (Complex.normSq_nonneg c)

/-- **The denominator of `H_ω`**: families null along `ω`. -/
def vecNull : Submodule ℂ (VecFam Y) where
  carrier := {ξ | ∀ ε : ℝ, 0 < ε → ∀ᶠ n in (ω : Filter ℕ), vecMass (ξ n) ≤ ε}
  zero_mem' := by
    intro ε hε
    refine Eventually.of_forall fun n ↦ ?_
    show vecMass (0 : (Y n) → ℂ) ≤ ε
    unfold vecMass
    simpa using hε.le
  add_mem' := by
    intro a b ha hb ε hε
    filter_upwards [ha (ε / 4) (by linarith), hb (ε / 4) (by linarith)]
      with n hna hnb
    show vecMass (a n + b n) ≤ ε
    have h1 : vecMass (a n + b n) ≤ 2 * vecMass (a n) + 2 * vecMass (b n) :=
      vecMass_add_le _ _
    linarith
  smul_mem' := by
    intro c a ha ε hε
    have hden : (0 : ℝ) < Complex.normSq c + 1 := by
      nlinarith [Complex.normSq_nonneg c]
    filter_upwards [ha (ε / (Complex.normSq c + 1)) (div_pos hε hden)] with n hn
    show vecMass (c • a n) ≤ ε
    rw [vecMass_smul]
    have hnn : (0 : ℝ) ≤ Complex.normSq c := Complex.normSq_nonneg c
    have hratio : Complex.normSq c / (Complex.normSq c + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    calc Complex.normSq c * vecMass (a n)
        ≤ Complex.normSq c * (ε / (Complex.normSq c + 1)) :=
          mul_le_mul_of_nonneg_left hn hnn
      _ = (Complex.normSq c / (Complex.normSq c + 1)) * ε := by ring
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hratio hε.le
      _ = ε := one_mul ε

/-- The denominator, viewed inside the numerator. -/
def vecNullIn : Submodule ℂ (vecBounded Y) :=
  Submodule.comap (vecBounded Y).subtype (vecNull Y ω)

/-- **The manuscript's `H_ω`**: the Hilbert-space ultraproduct of the coordinate
spaces `ℂ^{d_n}` along `ω`. -/
abbrev HOmega : Type := (vecBounded Y) ⧸ (vecNullIn Y ω)

end Space

/-! ## The inner product, on the numerator -/

section Inner

variable {Y : ℕ → FiniteModel} {ω : Ultrafilter ℕ}

theorem exists_tendsto_vecMass (ξ : vecBounded Y) :
    ∃ L : ℝ, Tendsto (fun n ↦ vecMass ((ξ : VecFam Y) n))
      (ω : Filter ℕ) (𝓝 L) := by
  obtain ⟨Cx, hx⟩ := ξ.2
  refine exists_tendsto_of_bounded ω (C := max Cx 0) fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (vecMass_nonneg _)]
  exact (hx n).trans (le_max_left _ _)

theorem exists_tendsto_vpairAt (ξ η : vecBounded Y) :
    ∃ L : ℂ, Tendsto (vpairAt (ξ : VecFam Y) (η : VecFam Y))
      (ω : Filter ℕ) (𝓝 L) := by
  obtain ⟨Cx, hx⟩ := ξ.2
  obtain ⟨Cy, hy⟩ := η.2
  refine exists_tendsto_of_bounded ω
    (C := Real.sqrt (max Cx 0) * Real.sqrt (max Cy 0)) fun n ↦ ?_
  refine (norm_vpairAt_le _ _ n).trans ?_
  have h1 : Real.sqrt (vecMass ((ξ : VecFam Y) n)) ≤ Real.sqrt (max Cx 0) :=
    Real.sqrt_le_sqrt ((hx n).trans (le_max_left _ _))
  have h2 : Real.sqrt (vecMass ((η : VecFam Y) n)) ≤ Real.sqrt (max Cy 0) :=
    Real.sqrt_le_sqrt ((hy n).trans (le_max_left _ _))
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **The inner product of `H_ω`**, on the numerator. -/
def uvinner (ξ η : vecBounded Y) : ℂ :=
  ulim ω (vpairAt (ξ : VecFam Y) (η : VecFam Y))

theorem uvinner_self (ξ : vecBounded Y) :
    uvinner (ω := ω) ξ ξ
      = ((ulim ω (fun n ↦ vecMass ((ξ : VecFam Y) n)) : ℝ) : ℂ) := by
  have hre : ulim ω (fun n ↦ ((vecMass ((ξ : VecFam Y) n) : ℝ) : ℂ))
      = ((ulim ω (fun n ↦ vecMass ((ξ : VecFam Y) n)) : ℝ) : ℂ) :=
    ulim_eq ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_ulim (exists_tendsto_vecMass ξ)))
  rw [uvinner, ← hre]
  exact ulim_congr (Eventually.of_forall fun n ↦ vpairAt_self _ n)
    (exists_tendsto_vpairAt ξ ξ)

theorem uvinner_self_nonneg (ξ : vecBounded Y) :
    0 ≤ (uvinner (ω := ω) ξ ξ).re := by
  rw [uvinner_self ξ, Complex.ofReal_re]
  exact ulim_nonneg (exists_tendsto_vecMass ξ) fun n ↦ vecMass_nonneg _

theorem uvinner_conj_symm (ξ η : vecBounded Y) :
    (starRingEnd ℂ) (uvinner (ω := ω) η ξ) = uvinner (ω := ω) ξ η := by
  have hcong : ∀ n,
      (starRingEnd ℂ) (vpairAt (η : VecFam Y) (ξ : VecFam Y) n)
        = vpairAt (ξ : VecFam Y) (η : VecFam Y) n :=
    fun n ↦ vpairAt_conj _ _ n
  rw [uvinner, uvinner, ← ulim_conj (exists_tendsto_vpairAt η ξ)]
  refine ulim_congr (Eventually.of_forall hcong) ?_
  exact ⟨_, (tendsto_ulim (exists_tendsto_vpairAt ξ η)).congr
    fun n ↦ (hcong n).symm⟩

theorem uvinner_add_right (ξ η ζ : vecBounded Y) :
    uvinner (ω := ω) ξ (η + ζ)
      = uvinner (ω := ω) ξ η + uvinner (ω := ω) ξ ζ := by
  rw [uvinner, uvinner, uvinner, ← ulim_add (exists_tendsto_vpairAt ξ η)
    (exists_tendsto_vpairAt ξ ζ)]
  refine ulim_congr (Eventually.of_forall fun n ↦ ?_)
    (exists_tendsto_vpairAt ξ (η + ζ))
  exact vpairAt_add_right _ _ _ n

theorem uvinner_smul_right (c : ℂ) (ξ η : vecBounded Y) :
    uvinner (ω := ω) ξ (c • η) = c * uvinner (ω := ω) ξ η := by
  rw [uvinner, uvinner, ← ulim_const_mul c (exists_tendsto_vpairAt ξ η)]
  refine ulim_congr (Eventually.of_forall fun n ↦ ?_)
    (exists_tendsto_vpairAt ξ (c • η))
  exact vpairAt_smul_right _ _ _ n

/-- A square root is dominated by its argument plus one. -/
theorem sqrt_le_add_one {M : ℝ} (hM : 0 ≤ M) : Real.sqrt M ≤ M + 1 := by
  have h1 : M ≤ (M + 1) ^ 2 := by nlinarith
  calc Real.sqrt M ≤ Real.sqrt ((M + 1) ^ 2) := Real.sqrt_le_sqrt h1
    _ = M + 1 := Real.sqrt_sq (by linarith)

/-- **The null step.**  A family null along `ω` pairs to zero against every
bounded family.  With Cauchy--Schwarz available this is a product of a factor
that vanishes along `ω` with one that is bounded. -/
theorem uvinner_eq_zero_of_vecNull {ζ η : vecBounded Y}
    (hζ : (ζ : VecFam Y) ∈ vecNull Y ω) : uvinner (ω := ω) ζ η = 0 := by
  obtain ⟨Cy, hy⟩ := η.2
  have hM : (0 : ℝ) ≤ max Cy 0 := le_max_right _ _
  have hMpos : (0 : ℝ) < max Cy 0 + 1 := by linarith
  have hMne : max Cy 0 + 1 ≠ 0 := ne_of_gt hMpos
  have hnorm : Tendsto
      (fun n ↦ ‖vpairAt (ζ : VecFam Y) (η : VecFam Y) n‖)
      (ω : Filter ℕ) (𝓝 ‖uvinner (ω := ω) ζ η‖) :=
    (tendsto_ulim (exists_tendsto_vpairAt ζ η)).norm
  refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  refine le_of_tendsto hnorm ?_
  filter_upwards [hζ ((ε / (max Cy 0 + 1)) ^ 2) (by positivity)] with n hn
  have h1 : Real.sqrt (vecMass ((ζ : VecFam Y) n)) ≤ ε / (max Cy 0 + 1) := by
    calc Real.sqrt (vecMass ((ζ : VecFam Y) n))
        ≤ Real.sqrt ((ε / (max Cy 0 + 1)) ^ 2) := Real.sqrt_le_sqrt hn
      _ = ε / (max Cy 0 + 1) := Real.sqrt_sq (by positivity)
  have h2 : Real.sqrt (vecMass ((η : VecFam Y) n)) ≤ max Cy 0 + 1 := by
    calc Real.sqrt (vecMass ((η : VecFam Y) n))
        ≤ Real.sqrt (max Cy 0) :=
          Real.sqrt_le_sqrt ((hy n).trans (le_max_left _ _))
      _ ≤ max Cy 0 + 1 := sqrt_le_add_one hM
  have hcancel : ε / (max Cy 0 + 1) * (max Cy 0 + 1) = ε := by field_simp
  calc ‖vpairAt (ζ : VecFam Y) (η : VecFam Y) n‖
      ≤ Real.sqrt (vecMass ((ζ : VecFam Y) n))
          * Real.sqrt (vecMass ((η : VecFam Y) n)) := norm_vpairAt_le _ _ n
    _ ≤ ε / (max Cy 0 + 1) * (max Cy 0 + 1) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = ε := hcancel

theorem uvinner_eq_zero_of_vecNull_right {ξ ζ : vecBounded Y}
    (hζ : (ζ : VecFam Y) ∈ vecNull Y ω) : uvinner (ω := ω) ξ ζ = 0 := by
  have h := uvinner_eq_zero_of_vecNull (η := ξ) hζ
  have hconj := uvinner_conj_symm ξ ζ (ω := ω)
  rw [h, map_zero] at hconj
  exact hconj.symm

theorem uvinner_add_left (ξ η ζ : vecBounded Y) :
    uvinner (ω := ω) (ξ + η) ζ
      = uvinner (ω := ω) ξ ζ + uvinner (ω := ω) η ζ := by
  have key : (starRingEnd ℂ) (uvinner (ω := ω) (ξ + η) ζ)
      = (starRingEnd ℂ) (uvinner (ω := ω) ξ ζ + uvinner (ω := ω) η ζ) := by
    rw [map_add, uvinner_conj_symm ζ (ξ + η), uvinner_conj_symm ζ ξ,
      uvinner_conj_symm ζ η]
    exact uvinner_add_right ζ ξ η
  exact star_injective key

theorem uvinner_smul_left (c : ℂ) (ξ η : vecBounded Y) :
    uvinner (ω := ω) (c • ξ) η
      = (starRingEnd ℂ) c * uvinner (ω := ω) ξ η := by
  rw [← uvinner_conj_symm (c • ξ) η, uvinner_smul_right c η ξ, map_mul,
    uvinner_conj_symm ξ η]

theorem uvinner_sub_left (ξ η ζ : vecBounded Y) :
    uvinner (ω := ω) (ξ - η) ζ
      = uvinner (ω := ω) ξ ζ - uvinner (ω := ω) η ζ := by
  have hsum : (ξ - η) + η = ξ := by abel
  have h := uvinner_add_left (ω := ω) (ξ - η) η ζ
  rw [hsum] at h
  rw [h]
  ring

theorem uvinner_sub_right (ξ η ζ : vecBounded Y) :
    uvinner (ω := ω) ξ (η - ζ)
      = uvinner (ω := ω) ξ η - uvinner (ω := ω) ξ ζ := by
  have hsum : (η - ζ) + ζ = η := by abel
  have h := uvinner_add_right (ω := ω) ξ (η - ζ) ζ
  rw [hsum] at h
  rw [h]
  ring

/-- **Definiteness.**  A bounded family of vanishing self-pairing is null along
`ω`, which is precisely membership in the denominator. -/
theorem vecNull_of_uvinner_self_eq_zero {ξ : vecBounded Y}
    (h : uvinner (ω := ω) ξ ξ = 0) : (ξ : VecFam Y) ∈ vecNull Y ω := by
  have hmass : ulim ω (fun n ↦ vecMass ((ξ : VecFam Y) n)) = 0 := by
    have hself := uvinner_self ξ (ω := ω)
    rw [h] at hself
    exact_mod_cast hself.symm
  intro ε hε
  filter_upwards [eventually_lt_of_ulim_eq_zero (exists_tendsto_vecMass ξ)
    hmass hε] with n hn
  exact hn.le

theorem uvinner_self_eq_zero_iff (ξ : vecBounded Y) :
    uvinner (ω := ω) ξ ξ = 0 ↔ (ξ : VecFam Y) ∈ vecNull Y ω :=
  ⟨fun h ↦ vecNull_of_uvinner_self_eq_zero h,
   fun h ↦ uvinner_eq_zero_of_vecNull h⟩

end Inner

/-! ## The descent, and the Hilbert-space structure -/

section Descent

variable (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ)

/-- **The inner product of `H_ω`**, on the quotient. -/
def hinner (x y : HOmega Y ω) : ℂ :=
  Quotient.liftOn₂' x y (fun ξ η ↦ uvinner (ω := ω) ξ η)
    (fun ξ η ξ' η' hξ hη ↦ by
      have hx : (Submodule.Quotient.mk ξ : HOmega Y ω)
          = Submodule.Quotient.mk ξ' := Quotient.sound' hξ
      have hy : (Submodule.Quotient.mk η : HOmega Y ω)
          = Submodule.Quotient.mk η' := Quotient.sound' hη
      rw [Submodule.Quotient.eq (vecNullIn Y ω)] at hx hy
      have h1 : uvinner (ω := ω) (ξ - ξ') η = 0 :=
        uvinner_eq_zero_of_vecNull hx
      have h2 : uvinner (ω := ω) ξ' (η - η') = 0 :=
        uvinner_eq_zero_of_vecNull_right hy
      rw [uvinner_sub_left] at h1
      rw [uvinner_sub_right] at h2
      linear_combination h1 + h2)

@[simp] theorem hinner_mk (ξ η : vecBounded Y) :
    hinner Y ω (Submodule.Quotient.mk ξ) (Submodule.Quotient.mk η)
      = uvinner (ω := ω) ξ η := rfl

theorem hinner_conj_symm (x y : HOmega Y ω) :
    (starRingEnd ℂ) (hinner Y ω y x) = hinner Y ω x y := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) x
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) y
  exact uvinner_conj_symm ξ η

theorem hinner_self_nonneg (x : HOmega Y ω) :
    0 ≤ RCLike.re (hinner Y ω x x) := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) x
  simpa using uvinner_self_nonneg ξ (ω := ω)

theorem hinner_add_left (x y z : HOmega Y ω) :
    hinner Y ω (x + y) z = hinner Y ω x z + hinner Y ω y z := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) x
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) y
  obtain ⟨ζ, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) z
  show uvinner (ω := ω) (ξ + η) ζ
      = uvinner (ω := ω) ξ ζ + uvinner (ω := ω) η ζ
  exact uvinner_add_left ξ η ζ

theorem hinner_smul_left (c : ℂ) (x y : HOmega Y ω) :
    hinner Y ω (c • x) y = (starRingEnd ℂ) c * hinner Y ω x y := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) x
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) y
  show uvinner (ω := ω) (c • ξ) η
      = (starRingEnd ℂ) c * uvinner (ω := ω) ξ η
  exact uvinner_smul_left c ξ η

theorem hinner_definite (x : HOmega Y ω) (h : hinner Y ω x x = 0) : x = 0 := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (vecNullIn Y ω) x
  rw [Submodule.Quotient.mk_eq_zero]
  exact (uvinner_self_eq_zero_iff ξ).1 h

/-- **`H_ω` itself**, exposed behind an opaque boundary so that its
inner-product structure is keyed to it rather than to every `Submodule`
quotient -- the same reason `KOmega` is introduced that way. -/
def VecOmega : Type := HOmega Y ω

noncomputable instance vecOmegaAddCommGroup : AddCommGroup (VecOmega Y ω) :=
  inferInstanceAs (AddCommGroup (HOmega Y ω))

noncomputable instance vecOmegaModule : Module ℂ (VecOmega Y ω) :=
  inferInstanceAs (Module ℂ (HOmega Y ω))

noncomputable instance vecOmegaInner : Inner ℂ (VecOmega Y ω) :=
  ⟨hinner Y ω⟩

noncomputable instance vecOmegaCore :
    InnerProductSpace.Core ℂ (VecOmega Y ω) where
  conj_inner_symm x y := hinner_conj_symm Y ω x y
  re_inner_nonneg x := hinner_self_nonneg Y ω x
  add_left x y z := hinner_add_left Y ω x y z
  smul_left x y r := hinner_smul_left Y ω r x y
  definite x h := hinner_definite Y ω x h

noncomputable instance vecOmegaNormedAddCommGroup :
    NormedAddCommGroup (VecOmega Y ω) :=
  (vecOmegaCore Y ω).toNormedAddCommGroup

/-- **`H_ω` is a complex inner product space**, with the ultralimit of the
coordinate inner products as its inner product.  This is the printed
"Hilbert-space ultraproduct of the coordinate spaces `ℂ^{d_n}`" as an object of
the theory. -/
noncomputable instance vecOmegaInnerProductSpace :
    InnerProductSpace ℂ (VecOmega Y ω) :=
  .ofCore _

/-- The class of a bounded family, as a vector of `H_ω`. -/
def mkV (ξ : vecBounded Y) : VecOmega Y ω := Submodule.Quotient.mk ξ

theorem mkV_surjective (x : VecOmega Y ω) :
    ∃ ξ : vecBounded Y, mkV Y ω ξ = x := by
  obtain ⟨ξ, hξ⟩ :=
    Submodule.Quotient.mk_surjective (vecNullIn Y ω) (show HOmega Y ω from x)
  exact ⟨ξ, hξ⟩

/-- The norm of `H_ω` is the square root of the ultralimit of the coordinate
masses. -/
theorem norm_mkV (ξ : vecBounded Y) :
    ‖mkV Y ω ξ‖ = Real.sqrt (ulim ω (fun n ↦ vecMass ((ξ : VecFam Y) n))) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  congr 1
  show RCLike.re (uvinner (ω := ω) ξ ξ) = _
  rw [uvinner_self ξ]
  simp

end Descent

end

end VectorHilbertUltraproduct
end GroupApproximation
