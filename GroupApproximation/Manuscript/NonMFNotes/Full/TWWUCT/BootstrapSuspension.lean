import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureBasic
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The suspension `C₀(ℝ, A)` of a separable non-unital C⋆-algebra

The class of separable C⋆-algebras `KK`-equivalent to commutative ones is closed under suspension
(Rosenberg--Schochet, Duke Math. J. 55 (1987), §2; Blackadar, *K-Theory for Operator Algebras*,
22.3.4).  This file supplies the concrete object-level part of that closure property, used for the
UCT input of `thm:fixed-radical-membership` in `non_mf_group_notes.tex`:

* `separableSpace_zeroAtInfty`: `C₀(ℝ, D)` is separable when `D` is (by truncation
  `f ↦ χ_N · f` to compact intervals, whose continuous-function spaces are separable);
* `SepNUCStarAlgebra.susp` and `SepNUCStarAlgebra.IsCommutative.susp`;
* `suspMap φ : C₀(ℝ, D) →⋆ₙₐ[ℂ] C₀(ℝ, E)` (postcomposition), with `suspMap_id`, `suspMap_comp`
  and homotopy invariance `suspMap_nHomotopic` (uniform continuity on the compact set where
  `‖f‖ ≥ ε`, via the tube lemma, and smallness elsewhere).
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWKK
open Filter Topology Set TopologicalSpace ZeroAtInfty

noncomputable section

section Separable

variable {D : Type*} [NormedAddCommGroup D]

/-- A pointwise bound gives a bound on the uniform distance in `C₀(ℝ, D)`. -/
theorem zeroAtInfty_dist_le_of_forall {f g : C₀(ℝ, D)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : ℝ, dist (f x) (g x) ≤ C) : dist f g ≤ C := by
  rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
  exact (BoundedContinuousFunction.dist_le hC).mpr h

/-- Outside a compact set a function vanishing at infinity has norm `< ε`: the compact set can be
taken to be `[-r, r]`. -/
theorem exists_norm_lt_of_abs_gt (f : C₀(ℝ, D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, ∀ x : ℝ, r < |x| → ‖f x‖ < ε := by
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp
    (Filter.tendsto_def.mp (zero_at_infty f) _ (Metric.ball_mem_nhds (0 : D) hε))
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp ht.isBounded
  refine ⟨r, fun x hx => ?_⟩
  have hxt : x ∉ t := fun hx' => by
    have h3 : dist x 0 ≤ r := hr hx'
    rw [Real.dist_0_eq_abs] at h3
    linarith
  have hfx : f x ∈ Metric.ball (0 : D) ε := hts hxt
  rw [Metric.mem_ball, dist_zero_right] at hfx
  exact hfx

/-- The cutoff `χ_N(x) = max 0 (min 1 (N - |x|))`: `1` on `[-(N-1), N-1]`, `0` off `(-N, N)`. -/
def suspCutoff (N : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 ((N : ℝ) - |x|))

theorem continuous_suspCutoff (N : ℕ) : Continuous (suspCutoff N) := by
  show Continuous fun x : ℝ => max 0 (min 1 ((N : ℝ) - |x|))
  exact continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem suspCutoff_nonneg (N : ℕ) (x : ℝ) : 0 ≤ suspCutoff N x := by
  unfold suspCutoff
  exact le_max_left _ _

theorem suspCutoff_le_one (N : ℕ) (x : ℝ) : suspCutoff N x ≤ 1 := by
  unfold suspCutoff
  exact max_le zero_le_one (min_le_left _ _)

theorem suspCutoff_eq_zero {N : ℕ} {x : ℝ} (hx : (N : ℝ) ≤ |x|) : suspCutoff N x = 0 := by
  unfold suspCutoff
  exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr hx))

theorem suspCutoff_eq_one {N : ℕ} {x : ℝ} (hx : |x| ≤ (N : ℝ) - 1) : suspCutoff N x = 1 := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) - |x| := by linarith
  unfold suspCutoff
  rw [min_eq_left h1]
  exact max_eq_right zero_le_one

theorem suspIcc_le (N : ℕ) : -(N : ℝ) ≤ (N : ℝ) :=
  neg_le_self (Nat.cast_nonneg N)

theorem coe_projIcc_of_abs_lt {N : ℕ} {x : ℝ} (hx : |x| < (N : ℝ)) :
    ((projIcc (-(N : ℝ)) (N : ℝ) (suspIcc_le N) x : ℝ)) = x := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hx
  rw [coe_projIcc, min_eq_right h2.le, max_eq_right h1.le]

theorem suspCutoff_smul_projIcc (N : ℕ) (g : ℝ → D) [Module ℝ D] (x : ℝ) :
    suspCutoff N x • g (projIcc (-(N : ℝ)) (N : ℝ) (suspIcc_le N) x : ℝ) =
      suspCutoff N x • g x := by
  rcases lt_or_ge |x| (N : ℝ) with hx | hx
  · rw [coe_projIcc_of_abs_lt hx]
  · rw [suspCutoff_eq_zero hx, zero_smul, zero_smul]

variable [NormedSpace ℝ D]

/-- **Truncation** `g ↦ χ_N · (g ∘ proj_{[-N, N]})`, from `C([-N, N], D)` to `C₀(ℝ, D)`. -/
def suspTrunc (N : ℕ) (g : C(Icc (-(N : ℝ)) (N : ℝ), D)) : C₀(ℝ, D) where
  toFun x := suspCutoff N x • g (projIcc (-(N : ℝ)) (N : ℝ) (suspIcc_le N) x)
  continuous_toFun :=
    (continuous_suspCutoff N).smul ((map_continuous g).comp continuous_projIcc)
  zero_at_infty' := by
    refine tendsto_nhds_of_eventually_eq
      (Filter.eventually_of_mem (isCompact_closedBall (0 : ℝ) (N : ℝ)).compl_mem_cocompact
        fun x hx => ?_)
    have hx2 : ¬ dist x 0 ≤ (N : ℝ) := hx
    rw [Real.dist_0_eq_abs] at hx2
    show suspCutoff N x • g (projIcc (-(N : ℝ)) (N : ℝ) (suspIcc_le N) x) = 0
    rw [suspCutoff_eq_zero (not_le.mp hx2).le, zero_smul]

theorem dist_suspTrunc_le (N : ℕ) (g g' : C(Icc (-(N : ℝ)) (N : ℝ), D)) :
    dist (suspTrunc N g) (suspTrunc N g') ≤ dist g g' := by
  refine zeroAtInfty_dist_le_of_forall dist_nonneg fun x => ?_
  show dist (suspCutoff N x • g (projIcc (-(N : ℝ)) (N : ℝ) (suspIcc_le N) x))
    (suspCutoff N x • g' (projIcc (-(N : ℝ)) (N : ℝ) (suspIcc_le N) x)) ≤ dist g g'
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (suspCutoff_nonneg N x)]
  exact (mul_le_of_le_one_left dist_nonneg (suspCutoff_le_one N x)).trans
    (ContinuousMap.dist_apply_le_dist _)

theorem continuous_suspTrunc (N : ℕ) : Continuous (suspTrunc (D := D) N) :=
  LipschitzWith.continuous (LipschitzWith.of_dist_le_mul (K := 1) fun g g' => by
    rw [NNReal.coe_one, one_mul]
    exact dist_suspTrunc_le N g g')

/-- Truncations approximate: `dist f (χ_N · f) < ε` for `N` large. -/
theorem exists_dist_suspTrunc_lt (f : C₀(ℝ, D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, dist f (suspTrunc N (f.toContinuousMap.restrict (Icc (-(N : ℝ)) (N : ℝ)))) < ε := by
  have h2 : 0 < ε / 2 := half_pos hε
  obtain ⟨r, hr⟩ := exists_norm_lt_of_abs_gt f h2
  obtain ⟨N, hN⟩ := exists_nat_ge (r + 1)
  refine ⟨N, lt_of_le_of_lt (zeroAtInfty_dist_le_of_forall h2.le fun x => ?_) (by linarith)⟩
  show dist (f x) (suspCutoff N x • f (projIcc (-(N : ℝ)) (N : ℝ) (suspIcc_le N) x : ℝ)) ≤
    ε / 2
  have hsub : f x - suspCutoff N x • f x = (1 - suspCutoff N x) • f x := by
    rw [sub_smul, one_smul]
  rw [suspCutoff_smul_projIcc N (⇑f) x, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (suspCutoff_le_one N x))]
  by_cases hx : |x| ≤ (N : ℝ) - 1
  · rw [suspCutoff_eq_one hx, sub_self, zero_mul]
    exact h2.le
  · have hfx : ‖f x‖ < ε / 2 := hr x (by linarith [not_le.mp hx])
    have hc : 1 - suspCutoff N x ≤ 1 := by linarith [suspCutoff_nonneg N x]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans hfx.le

/-- **`C₀(ℝ, D)` is separable** when `D` is. -/
instance separableSpace_zeroAtInfty [SeparableSpace D] : SeparableSpace C₀(ℝ, D) := by
  refine isSeparable_univ_iff.mp ?_
  have hU : IsSeparable (⋃ N : ℕ, range (suspTrunc (D := D) N)) :=
    IsSeparable.iUnion fun N => isSeparable_range (continuous_suspTrunc N)
  refine hU.closure.mono fun f _ => Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_dist_suspTrunc_lt f hε
  exact ⟨_, mem_iUnion.mpr ⟨N, mem_range_self _⟩, hN⟩

end Separable

/-- **The suspension** `SA = C₀(ℝ, A)` of a separable non-unital C⋆-algebra. -/
abbrev SepNUCStarAlgebra.susp (A : SepNUCStarAlgebra) : SepNUCStarAlgebra where
  carrier := C₀(ℝ, A)

/-- The suspension of a commutative algebra is commutative. -/
theorem SepNUCStarAlgebra.IsCommutative.susp {A : SepNUCStarAlgebra} (hA : A.IsCommutative) :
    A.susp.IsCommutative := by
  show ∀ x y : C₀(ℝ, A), x * y = y * x
  intro x y
  exact ZeroAtInftyContinuousMap.ext fun t => hA (x t) (y t)

section SuspMap

variable {D : Type*} {E : Type*} {G : Type*}
variable [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra G]

/-- A `⋆`-homomorphism is `1`-Lipschitz. -/
theorem dist_nonUnitalStarAlgHom_le (φ : D →⋆ₙₐ[ℂ] E) (a b : D) :
    dist (φ a) (φ b) ≤ dist a b := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub φ a b]
  exact NonUnitalStarAlgHom.norm_apply_le φ (a - b)

/-- **The suspended homomorphism** `Sφ : C₀(ℝ, D) → C₀(ℝ, E)`, `f ↦ φ ∘ f`. -/
def suspMap (φ : D →⋆ₙₐ[ℂ] E) : C₀(ℝ, D) →⋆ₙₐ[ℂ] C₀(ℝ, E) where
  toFun f :=
    { toFun := fun t => φ (f t)
      continuous_toFun := (continuous_nonUnitalStarAlgHom φ).comp (map_continuous f)
      zero_at_infty' := by
        have h : Tendsto (fun d : D => φ d) (𝓝 0) (𝓝 (φ 0)) :=
          (continuous_nonUnitalStarAlgHom φ).tendsto 0
        rw [map_zero] at h
        exact h.comp (zero_at_infty f) }
  map_smul' c f := ZeroAtInftyContinuousMap.ext fun t => map_smul φ c (f t)
  map_zero' := ZeroAtInftyContinuousMap.ext fun _ => map_zero φ
  map_add' f g := ZeroAtInftyContinuousMap.ext fun t => map_add φ (f t) (g t)
  map_mul' f g := ZeroAtInftyContinuousMap.ext fun t => map_mul φ (f t) (g t)
  map_star' f := ZeroAtInftyContinuousMap.ext fun t => map_star φ (f t)

theorem suspMap_apply (φ : D →⋆ₙₐ[ℂ] E) (f : C₀(ℝ, D)) (t : ℝ) :
    suspMap φ f t = φ (f t) :=
  rfl

theorem suspMap_id :
    suspMap (NonUnitalStarAlgHom.id ℂ D) = NonUnitalStarAlgHom.id ℂ C₀(ℝ, D) :=
  NonUnitalStarAlgHom.ext fun _ => ZeroAtInftyContinuousMap.ext fun _ => rfl

theorem suspMap_comp (φ : D →⋆ₙₐ[ℂ] E) (ψ : E →⋆ₙₐ[ℂ] G) :
    suspMap (ψ.comp φ) = (suspMap ψ).comp (suspMap φ) :=
  NonUnitalStarAlgHom.ext fun _ => ZeroAtInftyContinuousMap.ext fun _ => rfl

/-- **Continuity of suspended paths**: a pointwise-continuous path of `⋆`-homomorphisms suspends
to a pointwise-continuous path. -/
theorem continuous_suspMap_path {p : ℝ → (D →⋆ₙₐ[ℂ] E)} (hp : ∀ d : D, Continuous fun s => p s d)
    (f : C₀(ℝ, D)) : Continuous fun s => suspMap (p s) f := by
  refine continuous_iff_continuousAt.mpr fun s₀ => Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hη : 0 < ε / 4 := by linarith
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp
    (Filter.tendsto_def.mp (zero_at_infty f) _ (Metric.ball_mem_nhds (0 : D) hη))
  have hK : IsCompact (f '' t) := ht.image (map_continuous f)
  have hev : ∀ᶠ s in 𝓝 s₀, ∀ d ∈ f '' t, dist (p s d) (p s₀ d) < ε / 4 := by
    refine hK.eventually_forall_of_forall_eventually fun d _ => ?_
    have h3 : 0 < ε / 12 := by linarith
    have h1 : ∀ᶠ s in 𝓝 s₀, dist (p s d) (p s₀ d) < ε / 12 :=
      Metric.tendsto_nhds.mp ((hp d).tendsto s₀) _ h3
    have h2 : ∀ᶠ d' in 𝓝 d, dist d' d < ε / 12 := Metric.ball_mem_nhds d h3
    rw [nhds_prod_eq]
    refine (h1.prod_mk h2).mono fun z hz => ?_
    show dist (p z.1 z.2) (p s₀ z.2) < ε / 4
    have e1 := dist_nonUnitalStarAlgHom_le (p z.1) z.2 d
    have e2 := dist_nonUnitalStarAlgHom_le (p s₀) d z.2
    have e3 := dist_triangle4 (p z.1 z.2) (p z.1 d) (p s₀ d) (p s₀ z.2)
    rw [dist_comm d z.2] at e2
    linarith [hz.1, hz.2]
  refine hev.mono fun s hs => ?_
  show dist (suspMap (p s) f) (suspMap (p s₀) f) < ε
  refine lt_of_le_of_lt (zeroAtInfty_dist_le_of_forall (by linarith) fun x => ?_)
    (by linarith : ε / 2 < ε)
  show dist (p s (f x)) (p s₀ (f x)) ≤ ε / 2
  by_cases hx : x ∈ t
  · exact (hs (f x) (mem_image_of_mem f hx)).le.trans (by linarith)
  · have hfx : f x ∈ Metric.ball (0 : D) (ε / 4) := hts hx
    rw [Metric.mem_ball, dist_zero_right] at hfx
    have n1 := NonUnitalStarAlgHom.norm_apply_le (p s) (f x)
    have n2 := NonUnitalStarAlgHom.norm_apply_le (p s₀) (f x)
    have n3 := dist_le_norm_add_norm (p s (f x)) (p s₀ (f x))
    linarith

/-- **Suspension preserves homotopy.** -/
theorem suspMap_nHomotopic {φ ψ : D →⋆ₙₐ[ℂ] E} (h : NHomotopic φ ψ) :
    NHomotopic (suspMap φ) (suspMap ψ) := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun s => suspMap (p s), fun f => continuous_suspMap_path hp f, ?_, ?_⟩
  · show suspMap (p 0) = suspMap φ
    rw [h0]
  · show suspMap (p 1) = suspMap ψ
    rw [h1]

end SuspMap

end

end GroupApproximation.Full.TWWUCT.Bootstrap
