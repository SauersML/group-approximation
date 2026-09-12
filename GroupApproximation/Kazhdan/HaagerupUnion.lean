import GroupApproximation.Kazhdan.HaagerupKazhdanFinite
import GroupApproximation.Kazhdan.GaussianPositiveDefinite
import GroupApproximation.Kazhdan.KazhdanGNS
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GroupApproximation.Meta.AxiomGuard

/-!
# The Haagerup property passes to increasing unions

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1146--1147):

> Every countable subgroup of `GL_2` over a field has the Haagerup property …

A countable group is the increasing union of its finitely generated subgroups.  This module
proves that the Haagerup property passes to such unions, with no input beyond the repository's
GNS construction and Gaussian kernels.

* **Extension by zero.**  A positive-definite function on a subgroup `H ≤ G`, extended by zero,
  is positive-definite on `G` (`isPositiveDefinite_extendByZero`): it is the Gram kernel of the
  vectors `δ_{gH} ⊗ ξ_{h(g)}` in `ℓ²(G/H, 𝓗)`, where `𝓗` is the GNS space of the function and
  `g = (gH).out · h(g)`.
* **From approximations to a proper action.**  If every finite set admits a normalized
  positive-definite `φ` within `ε` of `1` on it, with `{φ ≥ 1/2}` finite, then a countable group
  has the Haagerup property (`hasHaagerupProperty_of_approx`): choose `φ_m` within `2^{-m}` of `1`
  on the first `m + 1` elements, take the GNS representations `π_m` with cyclic vectors `ξ_m`, and
  put `b g = (π_m g ξ_m − ξ_m)_m ∈ ℓ²(ℕ, 𝓗_m)`, so that `‖b g‖² = ∑_m (2 − 2 φ_m g)`.
* **Increasing unions** (`hasHaagerupProperty_of_iUnion`): the small Gaussians
  `exp (−t ‖b_N ·‖²)` of a proper cocycle on a large member `Γ_N`, extended by zero, are the
  approximations.
-/

namespace GroupApproximation
namespace Haagerup

open Delorme KazhdanGNS
open scoped InnerProductSpace ENNReal

universe u v

/-! ## Coordinatewise isometries of an `ℓ²`-sum -/

section LpIsometry

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

theorem memℓp_two_map (T : ∀ i, E i ≃ₗᵢ[ℝ] E i) (x : lp E 2) :
    Memℓp (fun i ↦ T i (x i)) 2 := by
  refine Memℓp.of_norm ?_
  have h := (lp.memℓp x).norm
  simpa only [LinearIsometryEquiv.norm_map] using h

/-- Coordinatewise linear isometries of an `ℓ²`-sum. -/
noncomputable def lpMap (T : ∀ i, E i ≃ₗᵢ[ℝ] E i) : lp E 2 ≃ₗᵢ[ℝ] lp E 2 where
  toFun x := ⟨fun i ↦ T i (x i), memℓp_two_map T x⟩
  invFun x := ⟨fun i ↦ (T i).symm (x i), memℓp_two_map (fun i ↦ (T i).symm) x⟩
  map_add' x y := lp.ext (funext fun i ↦ by
    show T i ((x + y) i) = T i (x i) + T i (y i)
    rw [lp.coeFn_add, Pi.add_apply, map_add])
  map_smul' c x := lp.ext (funext fun i ↦ by
    show T i ((c • x) i) = c • T i (x i)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul])
  left_inv x := lp.ext (funext fun i ↦ (T i).symm_apply_apply (x i))
  right_inv x := lp.ext (funext fun i ↦ (T i).apply_symm_apply (x i))
  norm_map' x := by
    have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    show ‖(⟨fun i ↦ T i (x i), memℓp_two_map T x⟩ : lp E 2)‖ = ‖x‖
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    exact congrArg (· ^ (1 / (2 : ℝ≥0∞).toReal))
      (tsum_congr fun i ↦ congrArg (· ^ (2 : ℝ≥0∞).toReal) ((T i).norm_map (x i)))

theorem lpMap_apply (T : ∀ i, E i ≃ₗᵢ[ℝ] E i) (x : lp E 2) (i : ι) :
    lpMap T x i = T i (x i) :=
  rfl

/-- The diagonal representation on an `ℓ²`-sum of orthogonal representations. -/
noncomputable def lpRepresentation {Γ : Type*} [Group Γ] (ρ : ∀ i, Γ →* (E i ≃ₗᵢ[ℝ] E i)) :
    Γ →* (lp E 2 ≃ₗᵢ[ℝ] lp E 2) where
  toFun g := lpMap fun i ↦ ρ i g
  map_one' := LinearIsometryEquiv.ext fun x ↦ lp.ext (funext fun i ↦
    congrArg (fun e : E i ≃ₗᵢ[ℝ] E i ↦ e (x i)) (map_one (ρ i)))
  map_mul' g h := LinearIsometryEquiv.ext fun x ↦ lp.ext (funext fun i ↦
    congrArg (fun e : E i ≃ₗᵢ[ℝ] E i ↦ e (x i)) (map_mul (ρ i) g h))

end LpIsometry

/-! ## Extension by zero from a subgroup -/

section ExtendByZero

open Classical

variable {G : Type u} [Group G]

/-- Extension by zero of a function on a subgroup. -/
noncomputable def extendByZero (H : Subgroup G) (f : H → ℝ) : G → ℝ :=
  fun g ↦ if hg : g ∈ H then f ⟨g, hg⟩ else 0

theorem extendByZero_of_mem (H : Subgroup G) (f : H → ℝ) {g : G} (hg : g ∈ H) :
    extendByZero H f g = f ⟨g, hg⟩ :=
  dif_pos hg

theorem extendByZero_of_not_mem (H : Subgroup G) (f : H → ℝ) {g : G} (hg : g ∉ H) :
    extendByZero H f g = 0 :=
  dif_neg hg

/-- The factor `h(g) = (gH).out⁻¹ g ∈ H`. -/
noncomputable def cosetFactor (H : Subgroup G) (g : G) : H :=
  ⟨(QuotientGroup.mk g : G ⧸ H).out⁻¹ * g,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : G ⧸ H))⟩

theorem cosetFactor_inv_mul {H : Subgroup G} {g h : G}
    (hgh : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk h) :
    (cosetFactor H g)⁻¹ * cosetFactor H h = ⟨g⁻¹ * h, QuotientGroup.eq.mp hgh⟩ := by
  apply Subtype.ext
  show ((QuotientGroup.mk g : G ⧸ H).out⁻¹ * g)⁻¹ * ((QuotientGroup.mk h : G ⧸ H).out⁻¹ * h) =
    g⁻¹ * h
  rw [hgh]
  group

/-- The Gram vectors `δ_{gH} ⊗ ξ_{h(g)}` realizing an extension by zero. -/
noncomputable def gramVector (H : Subgroup G) (p : PositiveDefiniteFunction H) (g : G) :
    lp (fun _ : G ⧸ H ↦ HilbertSpace p) 2 :=
  lp.single 2 (QuotientGroup.mk g : G ⧸ H) (kernelVector p (cosetFactor H g))

theorem inner_gramVector (H : Subgroup G) (p : PositiveDefiniteFunction H) (g h : G) :
    ⟪gramVector H p g, gramVector H p h⟫_ℝ = extendByZero H p.toFun (g⁻¹ * h) := by
  rw [gramVector, lp.inner_single_left]
  by_cases hgh : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk h
  · rw [gramVector, hgh, lp.single_apply_self, inner_kernelVector, cosetFactor_inv_mul hgh]
    exact (extendByZero_of_mem H p.toFun (QuotientGroup.eq.mp hgh)).symm
  · rw [gramVector, lp.single_apply_ne 2 _ _ hgh, inner_zero_right,
      extendByZero_of_not_mem H p.toFun fun hm ↦ hgh (QuotientGroup.eq.mpr hm)]

/-- **Extension by zero preserves positive-definiteness.** -/
theorem isPositiveDefinite_extendByZero (H : Subgroup G) {f : H → ℝ}
    (hf : KazhdanFiniteModel.IsPositiveDefinite f) :
    KazhdanFiniteModel.IsPositiveDefinite (extendByZero H f) := by
  let p : PositiveDefiniteFunction H := ⟨f, hf⟩
  have hker : ∀ g h : G,
      extendByZero H f (g⁻¹ * h) = ⟪gramVector H p g, gramVector H p h⟫_ℝ :=
    fun g h ↦ (inner_gramVector H p g h).symm
  refine ⟨fun g h ↦ (hker g h).trans ((real_inner_comm _ _).trans (hker h g).symm),
    fun F c ↦ ?_⟩
  have hsum : ∑ i ∈ F, ∑ j ∈ F, c i * c j * extendByZero H f (i⁻¹ * j) =
      ⟪∑ i ∈ F, c i • gramVector H p i, ∑ j ∈ F, c j • gramVector H p j⟫_ℝ := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hker]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsum]
  exact real_inner_self_nonneg

end ExtendByZero

/-! ## From positive-definite approximations to a proper affine action -/

section Approximation

variable {G : Type u} [Group G]

/-- `‖π g ξ − ξ‖² = 2 − 2 φ g` for the GNS triple of a normalized positive-definite `φ`. -/
theorem norm_sq_representation_sub_kernelVector (p : PositiveDefiniteFunction G)
    (hp1 : p.toFun 1 = 1) (g : G) :
    ‖representation p g (kernelVector p 1) - kernelVector p 1‖ ^ 2 = 2 - 2 * p.toFun g := by
  have hsymm : p.toFun g⁻¹ = p.toFun g := by
    have h := p.isPositiveDefinite.1 g 1
    simpa using h
  rw [representation_kernelVector, mul_one, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_kernelVector, inner_kernelVector, inner_kernelVector]
  simp only [inv_mul_cancel, mul_one, inv_one, hsymm, hp1]
  ring

/-- The `ℓ²`-sum of the GNS spaces of a sequence of positive-definite functions. -/
abbrev GNSSum (p : ℕ → PositiveDefiniteFunction G) : Type u :=
  lp (fun m ↦ HilbertSpace (p m)) 2

/-- The diagonal GNS representation on the `ℓ²`-sum. -/
noncomputable def gnsSumRepresentation (p : ℕ → PositiveDefiniteFunction G) :
    G →* (GNSSum p ≃ₗᵢ[ℝ] GNSSum p) :=
  lpRepresentation fun m ↦ representation (p m)

/-- The coordinates `π_m g ξ_m − ξ_m` of the displacement of the cyclic vectors. -/
noncomputable def gnsDisplacement (p : ℕ → PositiveDefiniteFunction G) (g : G) :
    ∀ m, HilbertSpace (p m) :=
  fun m ↦ representation (p m) g (kernelVector (p m) 1) - kernelVector (p m) 1

theorem memℓp_gnsDisplacement (p : ℕ → PositiveDefiniteFunction G)
    (hp1 : ∀ m, (p m).toFun 1 = 1) (g : G) (hsum : Summable fun m ↦ 2 - 2 * (p m).toFun g) :
    Memℓp (gnsDisplacement p g) 2 := by
  refine memℓp_gen ?_
  have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [e2, Real.rpow_two]
  exact hsum.congr fun m ↦ (norm_sq_representation_sub_kernelVector (p m) (hp1 m) g).symm

/-- The displacement vector in the `ℓ²`-sum. -/
noncomputable def gnsCocycle (p : ℕ → PositiveDefiniteFunction G)
    (hmem : ∀ g, Memℓp (gnsDisplacement p g) 2) (g : G) : GNSSum p :=
  ⟨gnsDisplacement p g, hmem g⟩

theorem isCocycle_gnsCocycle (p : ℕ → PositiveDefiniteFunction G)
    (hmem : ∀ g, Memℓp (gnsDisplacement p g) 2) :
    IsCocycle (gnsSumRepresentation p) (gnsCocycle p hmem) := by
  intro g h
  apply lp.ext
  funext m
  rw [lp.coeFn_add, Pi.add_apply]
  exact isCocycle_orbit (representation (p m)) (kernelVector (p m) 1) g h

/-- **Approximations give the Haagerup property.**  A countable group in which every finite set
admits a normalized positive-definite function within `ε` of `1` on it, and at least `1/2` only
on a finite set, admits a metrically proper affine isometric action. -/
theorem hasHaagerupProperty_of_approx [Countable G]
    (happrox : ∀ (S : Finset G) (ε : ℝ), 0 < ε →
      ∃ φ : G → ℝ, KazhdanFiniteModel.IsPositiveDefinite φ ∧ φ 1 = 1 ∧
        {g : G | 1 / 2 ≤ φ g}.Finite ∧ ∀ g ∈ S, 1 - φ g ≤ ε) :
    HasHaagerupProperty.{u, u} G := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  choose φ hφpd hφ1 hφfin hφS using fun m : ℕ ↦
    happrox ((Finset.range (m + 1)).image e) ((1 / 2 : ℝ) ^ m) (by positivity)
  set p : ℕ → PositiveDefiniteFunction G := fun m ↦ ⟨φ m, hφpd m⟩
  have hp1 : ∀ m, (p m).toFun 1 = 1 := hφ1
  have hnorm : ∀ (m : ℕ) (g : G), ‖gnsDisplacement p g m‖ ^ 2 = 2 - 2 * φ m g :=
    fun m g ↦ norm_sq_representation_sub_kernelVector (p m) (hp1 m) g
  have hsum : ∀ g : G, Summable fun m ↦ 2 - 2 * φ m g := by
    intro g
    obtain ⟨i, rfl⟩ := he g
    refine (summable_nat_add_iff i).mp ?_
    refine Summable.of_nonneg_of_le (fun m ↦ ?_) (fun m ↦ ?_)
      (summable_geometric_two.mul_left 2)
    · show 0 ≤ 2 - 2 * φ (m + i) (e i)
      rw [← hnorm]
      positivity
    · show 2 - 2 * φ (m + i) (e i) ≤ 2 * (1 / 2) ^ m
      have hmem : e i ∈ (Finset.range (m + i + 1)).image e :=
        Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
      have h1 := hφS (m + i) (e i) hmem
      have h2 : (1 / 2 : ℝ) ^ (m + i) ≤ (1 / 2) ^ m := by
        rw [pow_add]
        exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
      linarith
  have hmem : ∀ g, Memℓp (gnsDisplacement p g) 2 :=
    fun g ↦ memℓp_gnsDisplacement p hp1 g (hsum g)
  refine ⟨{ E := GNSSum p
            π := gnsSumRepresentation p
            b := gnsCocycle p hmem
            isCocycle := isCocycle_gnsCocycle p hmem
            proper := fun R ↦ ?_ }⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (R ^ 2)
  refine ((Finset.range N).finite_toSet.biUnion fun m _ ↦ hφfin m).subset ?_
  intro g hg
  have hg' : ‖gnsCocycle p hmem g‖ ≤ R := hg
  by_contra hno
  have hlt : ∀ m < N, φ m g < 1 / 2 := fun m hm ↦ by
    by_contra h
    exact hno (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hm)) (not_lt.mp h))
  have hnorm_sq : ‖gnsCocycle p hmem g‖ ^ 2 = ∑' m, (2 - 2 * φ m g) := by
    have hp2 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    have h := lp.norm_rpow_eq_tsum hp2 (gnsCocycle p hmem g)
    have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [e2, Real.rpow_two] at h
    rw [h]
    exact tsum_congr fun m ↦ hnorm m g
  have hlow : (N : ℝ) ≤ ∑ m ∈ Finset.range N, (2 - 2 * φ m g) := by
    have h := Finset.sum_le_sum fun m (hm : m ∈ Finset.range N) ↦
      (show (1 : ℝ) ≤ 2 - 2 * φ m g by linarith [hlt m (Finset.mem_range.mp hm)])
    simpa using h
  have hup : ∑ m ∈ Finset.range N, (2 - 2 * φ m g) ≤ ∑' m, (2 - 2 * φ m g) :=
    (hsum g).sum_le_tsum _ fun m _ ↦ by rw [← hnorm m g]; positivity
  have hR : ‖gnsCocycle p hmem g‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg' 2
  linarith

end Approximation

/-! ## Increasing unions -/

/-- **The Haagerup property passes to increasing unions.**  A countable group that is the union
of an increasing sequence of subgroups with the Haagerup property has the Haagerup property. -/
theorem hasHaagerupProperty_of_iUnion {G : Type u} [Group G] [Countable G]
    (Γ : ℕ → Subgroup G) (hmono : Monotone Γ) (hcover : ∀ g : G, ∃ n, g ∈ Γ n)
    (hΓ : ∀ n, HasHaagerupProperty.{u, v} (Γ n)) : HasHaagerupProperty.{u, u} G := by
  classical
  refine hasHaagerupProperty_of_approx fun S ε hε ↦ ?_
  choose n hn using hcover
  let N : ℕ := S.sup n
  have hSN : ∀ g ∈ S, g ∈ Γ N := fun g hg ↦ hmono (Finset.le_sup hg) (hn g)
  obtain ⟨A⟩ := hΓ N
  let bz : G → A.E := fun g ↦ if hg : g ∈ Γ N then A.b ⟨g, hg⟩ else 0
  let C : ℝ := ∑ g ∈ S, ‖bz g‖ ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  set t : ℝ := ε / (C + 1) with ht
  have htpos : 0 < t := div_pos hε (by linarith)
  let ψ : Γ N → ℝ := fun h ↦ Real.exp (-t * ‖A.b h‖ ^ 2)
  have hψ : KazhdanFiniteModel.IsPositiveDefinite ψ :=
    GaussianKernel.isPositiveDefinite_exp_neg_norm_sq A.b A.isCocycle.norm_inv_mul htpos.le
  refine ⟨extendByZero (Γ N) ψ, isPositiveDefinite_extendByZero (Γ N) hψ, ?_, ?_, ?_⟩
  · rw [extendByZero_of_mem (Γ N) ψ (Γ N).one_mem]
    show Real.exp (-t * ‖A.b 1‖ ^ 2) = 1
    rw [A.isCocycle.apply_one, norm_zero]
    simp
  · refine ((A.proper (1 / t + 1)).image Subtype.val).subset ?_
    intro g hg
    have hg' : 1 / 2 ≤ extendByZero (Γ N) ψ g := hg
    by_cases hgN : g ∈ Γ N
    · refine ⟨⟨g, hgN⟩, ?_, rfl⟩
      rw [extendByZero_of_mem (Γ N) ψ hgN] at hg'
      have hg'' : 1 / 2 ≤ Real.exp (-t * ‖A.b ⟨g, hgN⟩‖ ^ 2) := hg'
      have hmul : Real.exp (t * ‖A.b ⟨g, hgN⟩‖ ^ 2) * Real.exp (-t * ‖A.b ⟨g, hgN⟩‖ ^ 2) = 1 := by
        rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
      have hpos := Real.exp_pos (t * ‖A.b ⟨g, hgN⟩‖ ^ 2)
      have hexp : Real.exp (t * ‖A.b ⟨g, hgN⟩‖ ^ 2) ≤ 2 := by nlinarith
      have hlin := Real.add_one_le_exp (t * ‖A.b ⟨g, hgN⟩‖ ^ 2)
      have hsq : ‖A.b ⟨g, hgN⟩‖ ^ 2 ≤ 1 / t := by
        rw [le_div_iff₀ htpos]
        nlinarith
      show ‖A.b ⟨g, hgN⟩‖ ≤ 1 / t + 1
      have h0 := norm_nonneg (A.b ⟨g, hgN⟩)
      have h1t : 0 < 1 / t := by positivity
      nlinarith [sq_nonneg (‖A.b ⟨g, hgN⟩‖ - 1)]
    · rw [extendByZero_of_not_mem (Γ N) ψ hgN] at hg'
      norm_num at hg'
  · intro g hg
    have hgN := hSN g hg
    rw [extendByZero_of_mem (Γ N) ψ hgN]
    show 1 - Real.exp (-t * ‖A.b ⟨g, hgN⟩‖ ^ 2) ≤ ε
    have hlin := Real.add_one_le_exp (-t * ‖A.b ⟨g, hgN⟩‖ ^ 2)
    have hbz : bz g = A.b ⟨g, hgN⟩ := dif_pos hgN
    have hle : ‖A.b ⟨g, hgN⟩‖ ^ 2 ≤ C := by
      rw [← hbz]
      exact Finset.single_le_sum (f := fun g ↦ ‖bz g‖ ^ 2) (fun _ _ ↦ sq_nonneg _) hg
    have htC : t * ‖A.b ⟨g, hgN⟩‖ ^ 2 ≤ ε := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith

end Haagerup
end GroupApproximation

#audit_axioms GroupApproximation.Haagerup.isPositiveDefinite_extendByZero
#audit_axioms GroupApproximation.Haagerup.hasHaagerupProperty_of_approx
#audit_axioms GroupApproximation.Haagerup.hasHaagerupProperty_of_iUnion
