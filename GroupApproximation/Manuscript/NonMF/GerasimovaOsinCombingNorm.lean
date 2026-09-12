import GroupApproximation.Manuscript.NonMF.GerasimovaOsinCombingSum
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinFreeSemigroupNorm
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinSpectralRadius
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinGeometricInputs
import GroupApproximation.Manuscript.NonMF.DykemaDeLaHarpeTheorem14Proof
import GroupApproximation.Analysis.SubexponentialNormComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Gerasimova–Osin, Proposition 2.4, and the passage from Proposition 4.1

> **Proposition 2.4.** Let `G` be a group endowed with a pseudolength function `ℓ` and
> let `S` be a subset of `G`.  Suppose that there exists a symmetric `G`-equivariant
> generalized combing `C` such that `C(1,s) ∩ C(s,g) ∩ C(1,g) ≠ ∅` for all `s ∈ S` and
> `g ∈ G` and the associated growth functions `γ` and `ρ` take only finite values.  Then
> for every `a ∈ ℂG` and `n ∈ ℕ` such that `supp(a) ⊆ S ∩ B(n)`, we have
> `‖a‖ ≤ γ(ρ(n))^{3/2}‖a‖₂`.  In particular, if `S` is a subsemigroup of `G` and
> `lim_k (γ(ρ(k)))^{1/k} = 1`, then `r(a) = r₂(a)`.

* `norm_translationSum_apply_sq_le` — `‖aξ‖² ≤ γ(ρ(n))³ ‖a‖₂² ‖ξ‖²` for every
  `ξ ∈ ℓ²(G)`: for finitely supported `ξ` it is `GerasimovaOsinCombing.sum_sq_conv_le`
  applied to `|a|` and `|ξ|` (their proof of Proposition 2.4 from Lemma 2.5), and it passes
  to all of `ℓ²(G)` along the finite truncations;
* `norm_translationSum_le` — the operator norm bound;
* `hasL2SpectralRadiusProperty_of_combing` — the "in particular" clause, with the powers
  `aᵏ` written as translation sums over `Tᵏ` and constants polynomial in `k`;
* `gerasimovaOsinFreeSubsemigroupInput_of_proposition41` — their Corollary 5.5 for one
  group: Proposition 4.1 gives `GerasimovaOsinFreeSubsemigroupInput`, and with
  `dykemaDeLaHarpeTheorem14` it gives `GerasimovaOsinTheorem11Printed`
  (`gerasimovaOsinTheorem11Printed_of_proposition41`).

## Manuscript status

Reduction layer for `cor:regular-nonmf-algebra` ("Gerasimova and Osin give density of the
invertible elements, which is stable rank one").  Certifies no printed sentence on its
own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.GerasimovaOsinCombing
open GroupApproximation.Manuscript.NonMF.TorsionFree
open Filter Topology
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

/-! ## Coordinates and `ℓ²`-norms -/

theorem translationSum_apply (T : Finset G) (c : G → ℂ) (ξ : GroupHilbert G) (g : G) :
    ((translationSum T c : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G) ξ g
      = ∑ s ∈ T, c s * ξ (s⁻¹ * g) := by
  rw [translationSum, AddSubmonoidClass.coe_finsetSum, sum_apply,
    lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [SetLike.val_smul, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, reducedLeftRegular_apply]

omit [Group G] in
theorem norm_sq_eq_tsum (v : GroupHilbert G) : ‖v‖ ^ 2 = ∑' x, ‖v x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

omit [Group G] in
theorem norm_sq_eq_sum_of_support (v : GroupHilbert G) (U : Finset G)
    (hv : ∀ x, x ∉ U → v x = 0) : ‖v‖ ^ 2 = ∑ x ∈ U, ‖v x‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  exact tsum_eq_sum fun x hx => by rw [hv x hx, norm_zero, zero_pow two_ne_zero]

theorem reducedTwoNorm_translationSum_sq (T : Finset G) (c : G → ℂ) :
    reducedTwoNorm (translationSum T c) ^ 2 = ∑ s ∈ T, ‖c s‖ ^ 2 := by
  classical
  have hcoord : ∀ g : G,
      ((translationSum T c : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G)
        (deltaOne G) g = if g ∈ T then c g else 0 := by
    intro g
    rw [translationSum_apply]
    simp only [deltaOne_apply, inv_mul_eq_one, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
  rw [reducedTwoNorm, norm_sq_eq_sum_of_support _ T fun x hx => by rw [hcoord, if_neg hx]]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hcoord, if_pos hs]

/-! ## The norm estimate -/

section Estimate

variable (D : Combing G) (S : Set G)
  (htri : ∀ s ∈ S, ∀ g : G, (D.comb 1 s ∩ D.comb s g ∩ D.comb 1 g).Nonempty)

include htri

theorem norm_translationSum_apply_sq_le_of_support {n : ℕ} (T : Finset G)
    (hTS : ∀ s ∈ T, s ∈ S) (hTn : ∀ s ∈ T, D.len s ≤ n) (c : G → ℂ) (ξ : GroupHilbert G)
    (Y : Finset G) (hξY : ∀ t, t ∉ Y → ξ t = 0) :
    ‖((translationSum T c : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G) ξ‖ ^ 2
      ≤ (D.growth (D.radius n) : ℝ) ^ 3 * (∑ s ∈ T, ‖c s‖ ^ 2) * ‖ξ‖ ^ 2 := by
  classical
  have hsupp : ∀ g, g ∉ T * Y →
      ((translationSum T c : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G) ξ g
        = 0 := by
    intro g hg
    rw [translationSum_apply]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hnot : s⁻¹ * g ∉ Y := fun hmem => hg (by
      have hm := Finset.mul_mem_mul hs hmem
      rwa [mul_inv_cancel_left] at hm)
    rw [hξY _ hnot, mul_zero]
  rw [norm_sq_eq_sum_of_support _ (T * Y) hsupp, norm_sq_eq_sum_of_support ξ Y hξY]
  have hpt : ∀ g, ‖((translationSum T c : ReducedGroupCStar G) :
      GroupHilbert G →L[ℂ] GroupHilbert G) ξ g‖ ^ 2
        ≤ (∑ s ∈ T, ‖c s‖ * ‖ξ (s⁻¹ * g)‖) ^ 2 := by
    intro g
    rw [translationSum_apply]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun s _ => norm_mul _ _
  refine (Finset.sum_le_sum fun g _ => hpt g).trans ?_
  exact sum_sq_conv_le D S htri T hTS hTn Y (fun s => ‖c s‖) (fun t => ‖ξ t‖)
    (fun s => norm_nonneg _) (fun t ht => by rw [hξY t ht, norm_zero])

/-- **`‖aξ‖² ≤ γ(ρ(n))³ ‖a‖₂² ‖ξ‖²` for every `ξ ∈ ℓ²(G)`.** -/
theorem norm_translationSum_apply_sq_le {n : ℕ} (T : Finset G)
    (hTS : ∀ s ∈ T, s ∈ S) (hTn : ∀ s ∈ T, D.len s ≤ n) (c : G → ℂ) (ξ : GroupHilbert G) :
    ‖((translationSum T c : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G) ξ‖ ^ 2
      ≤ (D.growth (D.radius n) : ℝ) ^ 3 * (∑ s ∈ T, ‖c s‖ ^ 2) * ‖ξ‖ ^ 2 := by
  classical
  set a : GroupHilbert G →L[ℂ] GroupHilbert G :=
    ((translationSum T c : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G) with ha
  have hsum := lp.hasSum_single (p := 2) ENNReal.ofNat_ne_top ξ
  have htrunc : ∀ Y : Finset G, ∀ t, t ∉ Y →
      (∑ i ∈ Y, lp.single 2 i (ξ i) : GroupHilbert G) t = 0 := by
    intro Y t ht
    rw [lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [lp.coeFn_single, Pi.single_apply, if_neg]
    rintro rfl
    exact ht hi
  have hle : ∀ Y : Finset G, ‖a (∑ i ∈ Y, lp.single 2 i (ξ i))‖ ^ 2
      ≤ (D.growth (D.radius n) : ℝ) ^ 3 * (∑ s ∈ T, ‖c s‖ ^ 2) *
          ‖(∑ i ∈ Y, lp.single 2 i (ξ i) : GroupHilbert G)‖ ^ 2 :=
    fun Y => norm_translationSum_apply_sq_le_of_support D S htri T hTS hTn c _ Y (htrunc Y)
  have h1 : Tendsto (fun Y : Finset G => ‖a (∑ i ∈ Y, lp.single 2 i (ξ i))‖ ^ 2) atTop
      (𝓝 (‖a ξ‖ ^ 2)) :=
    ((a.continuous.tendsto ξ).comp hsum).norm.pow 2
  have h2 : Tendsto (fun Y : Finset G => (D.growth (D.radius n) : ℝ) ^ 3 *
      (∑ s ∈ T, ‖c s‖ ^ 2) * ‖(∑ i ∈ Y, lp.single 2 i (ξ i) : GroupHilbert G)‖ ^ 2) atTop
      (𝓝 ((D.growth (D.radius n) : ℝ) ^ 3 * (∑ s ∈ T, ‖c s‖ ^ 2) * ‖ξ‖ ^ 2)) :=
    tendsto_const_nhds.mul (hsum.norm.pow 2)
  exact le_of_tendsto_of_tendsto' h1 h2 hle

/-- **Gerasimova–Osin, Proposition 2.4**: `‖a‖ ≤ γ(ρ(n))^{3/2}‖a‖₂`. -/
theorem norm_translationSum_le {n : ℕ} (T : Finset G)
    (hTS : ∀ s ∈ T, s ∈ S) (hTn : ∀ s ∈ T, D.len s ≤ n) (c : G → ℂ) :
    ‖translationSum T c‖
      ≤ Real.sqrt ((D.growth (D.radius n) : ℝ) ^ 3) * reducedTwoNorm (translationSum T c) := by
  have hK : 0 ≤ (D.growth (D.radius n) : ℝ) ^ 3 := by positivity
  have h2 : 0 ≤ reducedTwoNorm (translationSum T c) := reducedTwoNorm_nonneg _
  change ‖((translationSum T c : ReducedGroupCStar G) :
      GroupHilbert G →L[ℂ] GroupHilbert G)‖ ≤ _
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) h2) fun ξ => ?_
  have hsq := norm_translationSum_apply_sq_le D S htri T hTS hTn c ξ
  rw [← reducedTwoNorm_translationSum_sq] at hsq
  have hrhs : (D.growth (D.radius n) : ℝ) ^ 3 * reducedTwoNorm (translationSum T c) ^ 2 * ‖ξ‖ ^ 2
      = (Real.sqrt ((D.growth (D.radius n) : ℝ) ^ 3) * reducedTwoNorm (translationSum T c)
          * ‖ξ‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hK]
  rw [hrhs] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h2) (norm_nonneg _)) two_ne_zero).mp hsq

end Estimate

/-! ## Powers of translation sums -/

theorem translationSum_mul [DecidableEq G] (T U : Finset G) (c d : G → ℂ) :
    translationSum T c * translationSum U d
      = translationSum (T * U)
          (fun g => ∑ p ∈ (T ×ˢ U).filter (fun p => p.1 * p.2 = g), c p.1 * d p.2) := by
  rw [translationSum, translationSum, Finset.sum_mul_sum,
    ← Finset.sum_product' (f := fun s v => (c s • reducedLeftRegular G s) *
      (d v • reducedLeftRegular G v)), translationSum]
  simp only [Finset.sum_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := T ×ˢ U) (t := T * U) (g := fun p => p.1 * p.2)
    (fun p hp => Finset.mul_mem_mul (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun p hp => ?_
  rw [smul_mul_smul_comm, ← reducedLeftRegular_mul, (Finset.mem_filter.mp hp).2]

theorem exists_translationSum_pow [DecidableEq G] (T : Finset G) (c : G → ℂ) (k : ℕ) :
    ∃ d : G → ℂ, translationSum T c ^ k = translationSum (T ^ k) d := by
  induction k with
  | zero =>
    refine ⟨fun _ => 1, ?_⟩
    have h1 : (1 : Finset G) = {1} :=
      Finset.ext fun x => by rw [Finset.mem_one, Finset.mem_singleton]
    rw [pow_zero, pow_zero, h1, translationSum]
    simp only [Finset.sum_singleton, one_smul, reducedLeftRegular_one]
  | succ k ih =>
    obtain ⟨d, hd⟩ := ih
    rw [pow_succ, hd, translationSum_mul, pow_succ]
    exact ⟨_, rfl⟩

theorem pow_subset_of_mul_closed [DecidableEq G] (T : Finset G) (P : Set G) (h1 : (1 : G) ∈ P)
    (hmul : ∀ x ∈ P, ∀ y ∈ T, x * y ∈ P) (k : ℕ) : ∀ x ∈ T ^ k, x ∈ P := by
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, Finset.mem_one] at hx
    rw [hx]
    exact h1
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hx
    exact hmul y (ih y hy) z hz

/-! ## The spectral radius property -/

/-- Constants polynomial in `k` have `k`-th roots tending to `1`. -/
theorem tendsto_rpow_inv_of_le_poly {c : ℕ → ℝ} (hc1 : ∀ k, 1 ≤ c k) {A : ℝ} {m : ℕ}
    (hA : 0 < A) (hcA : ∀ k, c k ≤ A * ((k : ℝ) + 1) ^ m) :
    Tendsto (fun k : ℕ ↦ c k ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hshift : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hbase : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) ^ (1 / (1 * ((k : ℝ) + 1) + -1))) atTop
      (𝓝 1) :=
    (tendsto_rpow_div_mul_add 1 1 (-1) (by norm_num)).comp hshift
  have hroot : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
    refine hbase.congr fun k => ?_
    congr 1
    ring
  have hAk : Tendsto (fun k : ℕ ↦ A ^ ((k : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := A)).rpow
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) (Or.inl hA.ne')
    simpa only [Function.comp_def, Real.rpow_zero] using h
  have hupper : Tendsto (fun k : ℕ ↦ A ^ ((k : ℝ)⁻¹) * (((k : ℝ) + 1) ^ ((k : ℝ)⁻¹)) ^ m)
      atTop (𝓝 1) := by
    simpa only [one_pow, mul_one] using hAk.mul (hroot.pow m)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun k => Real.one_le_rpow (hc1 k) (by positivity)) ?_
  refine Eventually.of_forall fun k => ?_
  have hpos : 0 ≤ ((k : ℝ) + 1) ^ m := by positivity
  calc c k ^ ((k : ℝ)⁻¹) ≤ (A * ((k : ℝ) + 1) ^ m) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (le_trans zero_le_one (hc1 k)) (hcA k) (by positivity)
    _ = A ^ ((k : ℝ)⁻¹) * (((k : ℝ) + 1) ^ ((k : ℝ)⁻¹)) ^ m := by
        rw [Real.mul_rpow hA.le hpos, ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
          mul_comm (m : ℝ) ((k : ℝ)⁻¹)]

/-- **The "in particular" clause of Proposition 2.4**, for linear growth bounds. -/
theorem hasL2SpectralRadiusProperty_of_combing (D : Combing G) (S : Set G)
    (htri : ∀ s ∈ S, ∀ g : G, (D.comb 1 s ∩ D.comb s g ∩ D.comb 1 g).Nonempty)
    (hlen1 : D.len 1 = 0) (T : Finset G) (h1S : (1 : G) ∈ S)
    (hmulS : ∀ x ∈ S, ∀ y ∈ T, x * y ∈ S) {κ : ℕ}
    (hgrowth : ∀ k : ℕ, (D.growth (D.radius k) : ℝ) ≤ κ * ((k : ℝ) + 1)) (n₀ : ℕ)
    (hTn : ∀ s ∈ T, D.len s ≤ n₀) (c : G → ℂ) :
    HasL2SpectralRadiusProperty (translationSum T c) := by
  classical
  rw [hasL2SpectralRadiusProperty_iff]
  have hpowS : ∀ k, ∀ x ∈ T ^ k, x ∈ S := pow_subset_of_mul_closed T S h1S hmulS
  have hpown : ∀ k : ℕ, ∀ x ∈ T ^ k, D.len x ≤ ((k * n₀ : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [pow_zero, Finset.mem_one] at hx
      rw [hx, hlen1]
      simp
    | succ k ih =>
      intro x hx
      rw [pow_succ] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hx
      calc D.len (y * z) ≤ D.len y + D.len z := D.len_mul y z
        _ ≤ ((k * n₀ : ℕ) : ℝ) + n₀ := add_le_add (ih y hy) (hTn z hz)
        _ = (((k + 1) * n₀ : ℕ) : ℝ) := by push_cast; ring
  have hbound : ∀ k, ‖translationSum T c ^ k‖
      ≤ ((D.growth (D.radius (k * n₀)) : ℝ) + 1) ^ 2 * reducedTwoNorm (translationSum T c ^ k) := by
    intro k
    obtain ⟨d, hd⟩ := exists_translationSum_pow T c k
    have h := norm_translationSum_le D S htri (n := k * n₀) (T ^ k) (hpowS k) (hpown k) d
    rw [← hd] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (reducedTwoNorm_nonneg _))
    have hK0 : 0 ≤ (D.growth (D.radius (k * n₀)) : ℝ) := Nat.cast_nonneg _
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (D.growth (D.radius (k * n₀)) : ℝ),
      mul_nonneg hK0 (sq_nonneg (D.growth (D.radius (k * n₀)) : ℝ))]
  have hpoly : ∀ k, ((D.growth (D.radius (k * n₀)) : ℝ) + 1) ^ 2
      ≤ ((κ * ((n₀ : ℝ) + 1) + 1) ^ 2) * ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hk := hgrowth (k * n₀)
    have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    have hlin : (D.growth (D.radius (k * n₀)) : ℝ) + 1
        ≤ (κ * ((n₀ : ℝ) + 1) + 1) * ((k : ℝ) + 1) := by
      have e : ((k * n₀ : ℕ) : ℝ) + 1 ≤ ((n₀ : ℝ) + 1) * ((k : ℝ) + 1) := by
        push_cast
        nlinarith
      have e2 : (κ : ℝ) * (((k * n₀ : ℕ) : ℝ) + 1) ≤ κ * (((n₀ : ℝ) + 1) * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left e hκ
      nlinarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlin 2
  have hc1 : Tendsto (fun k : ℕ ↦ (((D.growth (D.radius (k * n₀)) : ℝ) + 1) ^ 2) ^ ((k : ℝ)⁻¹))
      atTop (𝓝 1) :=
    tendsto_rpow_inv_of_le_poly (fun k => by
        have hK0 : 0 ≤ (D.growth (D.radius (k * n₀)) : ℝ) := Nat.cast_nonneg _
        nlinarith) (by positivity) hpoly
  exact limsup_rpow_le_of_le_mul (u := fun k => ‖translationSum T c ^ k‖)
    (v := fun k => reducedTwoNorm (translationSum T c ^ k))
    (c := fun k => ((D.growth (D.radius (k * n₀)) : ℝ) + 1) ^ 2)
    (fun k => norm_nonneg _) (fun k => reducedTwoNorm_nonneg _) (fun k => by positivity)
    hbound hc1
    (isCoboundedUnder_le_of_le atTop fun k => Real.rpow_nonneg (norm_nonneg _) _)
    ((isBoundedUnder_operatorSpectralRadius (translationSum T c)).mono_le
      (Eventually.of_forall fun k => reducedTwoNorm_pow_rpow_le (translationSum T c) k))

theorem hasL2SpectralRadiusProperty_zero :
    HasL2SpectralRadiusProperty (0 : ReducedGroupCStar G) := by
  have hne : ∀ k : ℕ, 1 ≤ k → ((k : ℝ)⁻¹) ≠ 0 := fun k hk =>
    inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hev : ∀ᶠ k : ℕ in atTop, ‖(0 : ReducedGroupCStar G) ^ k‖ ^ ((k : ℝ)⁻¹) = 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [zero_pow (by omega), norm_zero, Real.zero_rpow (hne k hk)]
  have hev2 : ∀ᶠ k : ℕ in atTop,
      reducedTwoNorm ((0 : ReducedGroupCStar G) ^ k) ^ ((k : ℝ)⁻¹) = 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [zero_pow (by omega), reducedTwoNorm, ZeroMemClass.coe_zero,
      zero_apply, norm_zero, Real.zero_rpow (hne k hk)]
  rw [HasL2SpectralRadiusProperty, l2SpectralRadius, operatorSpectralRadius,
    Filter.limsup_congr hev, Filter.limsup_congr hev2, limsup_const]

/-! ## Proposition 4.1 gives the geometric input -/

/-- **Gerasimova–Osin, Corollary 5.5, for one group**: Proposition 4.1 supplies the
hypothesis of Dykema–de la Harpe's criterion. -/
theorem gerasimovaOsinFreeSubsemigroupInput_of_proposition41
    (h41 : GerasimovaOsinProposition41Statement) : GerasimovaOsinFreeSubsemigroupInput := by
  intro G _ _ _ hrad F
  classical
  rcases F.eq_empty_or_nonempty with hF | hF
  · subst hF
    refine ⟨1, ?_, ?_⟩
    · intro w _ hw _ hne _ _
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil w hne
      simpa using hw x hx
    · intro m c γ hγ
      have hm : IsEmpty (Fin m) := ⟨fun i => by simpa using hγ i⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact hasL2SpectralRadiusProperty_zero
  · obtain ⟨ℓ, t, C, κ, hinv, hmul, hzero, hsymm, hequiv, hfree, htri, hfin, hradius⟩ :=
      h41 G hrad F hF
    refine ⟨t, hfree, ?_⟩
    intro m c γ hγ
    rw [finSum_eq_translationSum]
    let D : Combing G :=
      { len := ℓ
        comb := C
        growth := fun n => κ * (n + 1)
        radius := fun n => κ * (n + 1)
        comb_symm := hsymm
        comb_equivariant := hequiv
        len_inv := hinv
        len_mul := hmul
        ball_finite := fun n g => (hfin n g).1
        ball_card := fun n g => (hfin n g).2
        comb_len := fun n g hg x hx => by
          have h := hradius n g hg x hx
          push_cast
          exact h }
    have hTS : ∀ s ∈ Finset.univ.image γ,
        s ∈ Subsemigroup.closure ((fun x => t * x) '' (F : Set G)) := by
      intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
      exact Subsemigroup.subset_closure (hγ i)
    refine hasL2SpectralRadiusProperty_of_combing D
      ((Subsemigroup.closure ((fun x => t * x) '' (F : Set G)) : Set G) ∪ {1})
      (fun s hs g => htri g s hs)
      ((hzero 1).mpr rfl) (Finset.univ.image γ) (Set.mem_union_right _ (Set.mem_singleton 1))
      ?_ (κ := κ * κ + κ) ?_ ((Finset.univ.image γ).sup fun s => ⌈ℓ s⌉₊) ?_ _
    · intro x hx y hy
      refine Set.mem_union_left _ ?_
      rcases hx with hx | hx
      · exact Subsemigroup.mul_mem _ hx (hTS y hy)
      · rw [Set.mem_singleton_iff.mp hx, one_mul]
        exact hTS y hy
    · intro k
      show ((κ * (κ * (k + 1) + 1) : ℕ) : ℝ) ≤ ((κ * κ + κ : ℕ) : ℝ) * ((k : ℝ) + 1)
      push_cast
      have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith
    · intro s hs
      have h1 : ⌈ℓ s⌉₊ ≤ (Finset.univ.image γ).sup fun s => ⌈ℓ s⌉₊ :=
        Finset.le_sup (f := fun s => ⌈ℓ s⌉₊) hs
      calc ℓ s ≤ ⌈ℓ s⌉₊ := Nat.le_ceil _
        _ ≤ _ := by exact_mod_cast h1

/-- **`GerasimovaOsinTheorem11Printed` from Gerasimova–Osin's Proposition 4.1.** -/
theorem gerasimovaOsinTheorem11Printed_of_proposition41
    (h41 : GerasimovaOsinProposition41Statement) : GerasimovaOsinTheorem11Printed :=
  gerasimovaOsinTheorem11Printed_of_freeSubsemigroupInput
    (gerasimovaOsinFreeSubsemigroupInput_of_proposition41 h41)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms norm_translationSum_apply_sq_le
#audit_axioms norm_translationSum_le
#audit_axioms hasL2SpectralRadiusProperty_of_combing
#audit_axioms gerasimovaOsinFreeSubsemigroupInput_of_proposition41
#audit_axioms gerasimovaOsinTheorem11Printed_of_proposition41
