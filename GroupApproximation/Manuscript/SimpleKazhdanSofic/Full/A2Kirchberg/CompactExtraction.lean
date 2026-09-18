import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.Sequences

/-!
Fork (lane A2Kirchberg) of the never-wired `GroupApproximation/Analysis/KirchbergCompactExtraction.lean`,
for Kirchberg, Math. Ann. 299 (1994), Theorem 1.1 (property (T) and the factorization property
imply residual finiteness), the Kirchberg--Thom step of table row A2 of
`simple_kazhdan_sofic_group.tex` (l.54--60; bibitem l.864--866).

# Compact intertwiners and finite-dimensional subrepresentations

Let `σ` be an orthogonal representation of a group on a complete real Hilbert
space `K`, and let `T` be a compact operator commuting with `σ`.  If an element
`h` acts trivially on every finite-dimensional invariant subspace, then `h` acts
trivially on the range of `T`.

This is the compactness step of Kirchberg's Theorem 1.1: an invariant vector of
the tensor square is a compact intertwiner, and its range is spanned by
finite-dimensional subrepresentations.

* `exists_eigenvector_adjoint_comp_self`: a nonzero compact `S` gives an
  eigenvector of `S† S` for the eigenvalue `‖S‖²`, by a maximizing sequence and
  compactness.
* `finiteDimensional_eigenspace`: the eigenspaces of a compact operator for
  nonzero eigenvalues are finite-dimensional.
* `apply_eq_of_forall_finiteDimensional_fixed`: the statement above.  Let `M` be
  the closure of the span of the finite-dimensional invariant subspaces.  The
  compact intertwiner `S = T (1 - P_M)` has `S† S = 0`, since otherwise an
  eigenspace of `S† S` would be a finite-dimensional invariant subspace inside
  `M^⊥`.  So `T = T P_M` has range in `M`, where `h` acts trivially.
-/

namespace GroupApproximation.Full.A2Kirchberg.CompactExtraction

open Filter Topology

universe u v

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `‖S† (S x)‖² ≤ ‖S‖² ‖S x‖²`. -/
theorem norm_adjoint_apply_sq_le (S : K →L[ℝ] K) (x : K) :
    ‖ContinuousLinearMap.adjoint S (S x)‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖S x‖ ^ 2 := by
  have h : ‖ContinuousLinearMap.adjoint S (S x)‖ ≤ ‖S‖ * ‖S x‖ := by
    have := (ContinuousLinearMap.adjoint S).le_opNorm (S x)
    rwa [LinearIsometryEquiv.norm_map] at this
  calc ‖ContinuousLinearMap.adjoint S (S x)‖ ^ 2 ≤ (‖S‖ * ‖S x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ‖S‖ ^ 2 * ‖S x‖ ^ 2 := mul_pow _ _ _

/-- **A nonzero compact operator gives an eigenvector of `S† S` for `‖S‖²`.** -/
theorem exists_eigenvector_adjoint_comp_self (S : K →L[ℝ] K) (hS : IsCompactOperator S)
    (hne : S ≠ 0) :
    ∃ y : K, y ≠ 0 ∧ ContinuousLinearMap.adjoint S (S y) = ‖S‖ ^ 2 • y := by
  have hSpos : 0 < ‖S‖ := norm_pos_iff.mpr hne
  set c : ℝ := ‖S‖ ^ 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  let r : ℕ → ℝ := fun n ↦ ‖S‖ - ‖S‖ / ((n : ℝ) + 2)
  have hr_lt : ∀ n, r n < ‖S‖ := fun n ↦ by
    have : 0 < ‖S‖ / ((n : ℝ) + 2) := by positivity
    show ‖S‖ - ‖S‖ / ((n : ℝ) + 2) < ‖S‖
    linarith
  have hr_half : ∀ n, ‖S‖ / 2 ≤ r n := fun n ↦ by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : ‖S‖ / ((n : ℝ) + 2) ≤ ‖S‖ / 2 :=
      div_le_div_of_nonneg_left hSpos.le (by norm_num) (by linarith)
    show ‖S‖ / 2 ≤ ‖S‖ - ‖S‖ / ((n : ℝ) + 2)
    linarith
  choose x hxnorm hxlow using fun n ↦ S.exists_lt_apply_of_lt_opNorm (hr_lt n)
  have hxle : ∀ n, ‖S (x n)‖ ≤ ‖S‖ := fun n ↦
    (S.le_opNorm (x n)).trans (mul_le_of_le_one_right hSpos.le (hxnorm n).le)
  have hdefect : ∀ n, ‖ContinuousLinearMap.adjoint S (S (x n)) - c • x n‖ ^ 2
      ≤ c * (c - ‖S (x n)‖ ^ 2) := by
    intro n
    have hinner : ⟪ContinuousLinearMap.adjoint S (S (x n)), x n⟫ = ‖S (x n)‖ ^ 2 := by
      rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
    have hB : ‖ContinuousLinearMap.adjoint S (S (x n))‖ ^ 2 ≤ c * ‖S (x n)‖ ^ 2 := by
      rw [hc]
      exact norm_adjoint_apply_sq_le S (x n)
    have hxsq : ‖x n‖ ^ 2 ≤ 1 := by
      have h1 := (hxnorm n).le
      have h0 := norm_nonneg (x n)
      nlinarith
    have hcx : c ^ 2 * ‖x n‖ ^ 2 ≤ c ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hxsq (le_of_lt (pow_pos hcpos 2))
    rw [norm_sub_sq_real, real_inner_smul_right, hinner, norm_smul, Real.norm_eq_abs,
      abs_of_pos hcpos, mul_pow]
    nlinarith
  have hlow : Tendsto (fun n ↦ c - ‖S (x n)‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ ‖S‖ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hr_tend : Tendsto r atTop (𝓝 ‖S‖) := by
      have := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ‖S‖) atTop (𝓝 ‖S‖)).sub h1
      simpa using this
    have hupper : Tendsto (fun n ↦ c - r n ^ 2) atTop (𝓝 0) := by
      have := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c)).sub (hr_tend.pow 2)
      rwa [← hc, sub_self] at this
    refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hupper
    · have := pow_le_pow_left₀ (norm_nonneg _) (hxle n) 2
      linarith
    · have h2 : 0 ≤ r n := le_trans (by positivity) (hr_half n)
      have := pow_le_pow_left₀ h2 (hxlow n).le 2
      linarith
  have hdef0 : Tendsto (fun n ↦ ‖ContinuousLinearMap.adjoint S (S (x n)) - c • x n‖)
      atTop (𝓝 0) := by
    have hsq : Tendsto (fun n ↦ Real.sqrt (c * (c - ‖S (x n)‖ ^ 2))) atTop (𝓝 0) := by
      have h0 := hlow.const_mul c
      rw [mul_zero] at h0
      have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
      rwa [Real.sqrt_zero] at h1
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hsq
    have := Real.abs_le_sqrt (hdefect n)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  let B : K →L[ℝ] K := ContinuousLinearMap.adjoint S ∘L S
  have hBcomp : IsCompactOperator (B : K →ₗ[ℝ] K) := hS.clm_comp (ContinuousLinearMap.adjoint S)
  have hcpt := IsCompactOperator.isCompact_closure_image_closedBall hBcomp 1
  have hmem : ∀ n, B (x n) ∈ closure ((B : K →ₗ[ℝ] K) '' Metric.closedBall 0 1) := fun n ↦
    subset_closure ⟨x n, mem_closedBall_zero_iff.mpr (hxnorm n).le, rfl⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  have hd : Tendsto (fun n ↦ B (x (φ n)) - c • x (φ n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hdef0.comp hφ.tendsto_atTop
  have hlim2 : Tendsto (fun n ↦ c • x (φ n)) atTop (𝓝 y) := by
    have := hlim.sub hd
    simpa [Function.comp_def] using this
  have hBy : B y = c • y := by
    have h1 : Tendsto (fun n ↦ B (c • x (φ n))) atTop (𝓝 (B y)) :=
      (B.continuous.tendsto y).comp hlim2
    have h2 : Tendsto (fun n ↦ B (c • x (φ n))) atTop (𝓝 (c • y)) := by
      simp only [map_smul]
      exact hlim.const_smul c
    exact tendsto_nhds_unique h1 h2
  have hy0 : y ≠ 0 := by
    intro hy
    have h1 : Tendsto (fun n ↦ ‖S (c • x (φ n))‖) atTop (𝓝 0) := by
      have := ((S.continuous.tendsto y).comp hlim2).norm
      rwa [hy, map_zero, norm_zero] at this
    have h2 : ∀ n, c * (‖S‖ / 2) ≤ ‖S (c • x (φ n))‖ := by
      intro n
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_left ((hr_half (φ n)).trans (hxlow (φ n)).le) hcpos.le
    have h3 : c * (‖S‖ / 2) ≤ 0 := ge_of_tendsto' h1 h2
    have h4 : 0 < c * (‖S‖ / 2) := mul_pos hcpos (half_pos hSpos)
    linarith
  exact ⟨y, hy0, hBy⟩

omit [CompleteSpace K] in
/-- **Eigenspaces of a compact operator for nonzero eigenvalues are
finite-dimensional.** -/
theorem finiteDimensional_eigenspace (B : K →L[ℝ] K) (hB : IsCompactOperator B) {c : ℝ}
    (hc : c ≠ 0) :
    FiniteDimensional ℝ (LinearMap.ker ((B : K →ₗ[ℝ] K) - c • LinearMap.id)) := by
  set W : Submodule ℝ K := LinearMap.ker ((B : K →ₗ[ℝ] K) - c • LinearMap.id) with hW
  have hmemW : ∀ v : K, v ∈ W ↔ B v = c • v := fun v ↦ by
    simp [hW, sub_eq_zero]
  have hinv : ∀ v ∈ W, (B : K →ₗ[ℝ] K) v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    simp only [ContinuousLinearMap.coe_coe, hv, map_smul]
  have hclosed : IsClosed (W : Set K) := by
    have hset : (W : Set K) = {v | B v = c • v} := Set.ext hmemW
    rw [hset]
    exact isClosed_eq B.continuous (continuous_const_smul c)
  have hres : IsCompactOperator ((B : K →ₗ[ℝ] K).restrict hinv) :=
    IsCompactOperator.restrict hB hinv hclosed
  have hfun : (id : W → W) = c⁻¹ • ⇑((B : K →ₗ[ℝ] K).restrict hinv) := by
    funext w
    apply Subtype.ext
    have hw : B (w : K) = c • (w : K) := (hmemW w).1 w.2
    simp [hw, inv_smul_smul₀ hc]
  have hid : IsCompactOperator (id : W → W) := by
    rw [hfun]
    exact hres.smul c⁻¹
  exact FiniteDimensional.of_isCompactOperator_id hid

variable {G : Type u} [Group G]

/-- A submodule is invariant under the representation. -/
def IsInvariant (σ : G →* (K ≃ₗᵢ[ℝ] K)) (W : Submodule ℝ K) : Prop :=
  ∀ g : G, ∀ x ∈ W, σ g x ∈ W

/-- **Compact intertwiners have range in the finite-dimensional
subrepresentations.**  If `h` fixes every finite-dimensional invariant subspace
pointwise, it fixes the range of every compact operator commuting with `σ`. -/
theorem apply_eq_of_forall_finiteDimensional_fixed
    (σ : G →* (K ≃ₗᵢ[ℝ] K)) (T : K →L[ℝ] K) (hT : IsCompactOperator T)
    (hcomm : ∀ (g : G) (v : K), T (σ g v) = σ g (T v)) (h : G)
    (hfix : ∀ W : Submodule ℝ K, FiniteDimensional ℝ W → IsInvariant σ W →
      ∀ v ∈ W, σ h v = v) (x : K) :
    σ h (T x) = T x := by
  classical
  let ι := {W : Submodule ℝ K // FiniteDimensional ℝ W ∧ IsInvariant σ W}
  set N : Submodule ℝ K := ⨆ W : ι, W.1 with hN
  set M : Submodule ℝ K := N.topologicalClosure with hM
  have hcancel : ∀ (g : G) (v : K), σ g⁻¹ (σ g v) = v := fun g v ↦ by simp
  have hcancel' : ∀ (g : G) (v : K), σ g (σ g⁻¹ v) = v := fun g v ↦ by simp
  have hNinv : ∀ (g : G), ∀ v ∈ N, σ g v ∈ N := by
    intro g v hv
    refine Submodule.iSup_induction (fun W : ι ↦ W.1) (motive := fun v ↦ σ g v ∈ N) hv
      (fun W w hw ↦ Submodule.mem_iSup_of_mem W (W.2.2 g w hw)) (by simp) ?_
    intro a b ha hb
    rw [map_add]
    exact N.add_mem ha hb
  have hNfix : ∀ v ∈ N, σ h v = v := by
    intro v hv
    refine Submodule.iSup_induction (fun W : ι ↦ W.1) (motive := fun v ↦ σ h v = v) hv
      (fun W w hw ↦ hfix W.1 W.2.1 W.2.2 w hw) (by simp) ?_
    intro a b ha hb
    rw [map_add, ha, hb]
  have hNT : ∀ v ∈ N, T v ∈ N := by
    intro v hv
    refine Submodule.iSup_induction (fun W : ι ↦ W.1) (motive := fun v ↦ T v ∈ N) hv ?_
      (by simp) ?_
    · intro W w hw
      haveI : FiniteDimensional ℝ W.1 := W.2.1
      have hinv : IsInvariant σ (W.1.map (T : K →ₗ[ℝ] K)) := by
        rintro g _ ⟨u, hu, rfl⟩
        exact ⟨σ g u, W.2.2 g u hu, hcomm g u⟩
      exact Submodule.mem_iSup_of_mem
        (⟨W.1.map (T : K →ₗ[ℝ] K), inferInstance, hinv⟩ : ι) ⟨w, hw, rfl⟩
    · intro a b ha hb
      rw [map_add]
      exact N.add_mem ha hb
  have hMcoe : (M : Set K) = closure (N : Set K) := N.topologicalClosure_coe
  have hMinv : ∀ (g : G), ∀ v ∈ M, σ g v ∈ M := by
    intro g v hv
    rw [← SetLike.mem_coe, hMcoe] at hv ⊢
    exact map_mem_closure (σ g).continuous hv fun w hw ↦ hNinv g w hw
  have hMfix : ∀ v ∈ M, σ h v = v := by
    intro v hv
    rw [← SetLike.mem_coe, hMcoe] at hv
    exact closure_minimal (fun w hw ↦ hNfix w hw)
      (isClosed_eq (σ h).continuous continuous_id) hv
  have hMT : ∀ v ∈ M, T v ∈ M := by
    intro v hv
    rw [← SetLike.mem_coe, hMcoe] at hv ⊢
    exact map_mem_closure T.continuous hv fun w hw ↦ hNT w hw
  haveI : CompleteSpace M := N.isClosed_topologicalClosure.completeSpace_coe
  have hMorth : ∀ (g : G), ∀ v ∈ Mᗮ, σ g v ∈ Mᗮ := by
    intro g v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    calc ⟪u, σ g v⟫ = ⟪σ g⁻¹ u, σ g⁻¹ (σ g v)⟫ := by rw [(σ g⁻¹).inner_map_map]
      _ = ⟪σ g⁻¹ u, v⟫ := by rw [hcancel]
      _ = 0 := Submodule.inner_right_of_mem_orthogonal (hMinv g⁻¹ u hu) hv
  set P : K →L[ℝ] K := M.starProjection with hP
  have hPfix : ∀ w ∈ M, P w = w := fun w hw ↦ (Submodule.starProjection_eq_self_iff).2 hw
  have hPmem : ∀ w, P w ∈ M := fun w ↦ M.starProjection_apply_mem w
  have hPcomm : ∀ (g : G) (v : K), P (σ g v) = σ g (P v) := by
    intro g v
    refine Submodule.eq_starProjection_of_mem_orthogonal (hMinv g _ (hPmem v)) ?_
    rw [← map_sub]
    exact hMorth g _ (Submodule.sub_starProjection_mem_orthogonal v)
  set S : K →L[ℝ] K := T ∘L (ContinuousLinearMap.id ℝ K - P) with hS
  have hSapply : ∀ v, S v = T (v - P v) := fun v ↦ rfl
  have hScomp : IsCompactOperator S := hT.comp_clm (ContinuousLinearMap.id ℝ K - P)
  have hScomm : ∀ (g : G) (v : K), S (σ g v) = σ g (S v) := by
    intro g v
    rw [hSapply, hSapply, hPcomm, ← map_sub, hcomm]
  have hSadjM : ∀ u : K, ContinuousLinearMap.adjoint S u ∈ Mᗮ := by
    intro u
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [ContinuousLinearMap.adjoint_inner_right, hSapply, hPfix w hw, sub_self, map_zero,
      inner_zero_left]
  have hSadjcomm : ∀ (g : G) (v : K), ContinuousLinearMap.adjoint S (σ g v)
      = σ g (ContinuousLinearMap.adjoint S v) := by
    intro g v
    refine ext_inner_right ℝ fun w ↦ ?_
    calc ⟪ContinuousLinearMap.adjoint S (σ g v), w⟫ = ⟪σ g v, S w⟫ :=
          ContinuousLinearMap.adjoint_inner_left S w (σ g v)
      _ = ⟪σ g⁻¹ (σ g v), σ g⁻¹ (S w)⟫ := by rw [(σ g⁻¹).inner_map_map]
      _ = ⟪v, S (σ g⁻¹ w)⟫ := by rw [hcancel, hScomm]
      _ = ⟪ContinuousLinearMap.adjoint S v, σ g⁻¹ w⟫ :=
          (ContinuousLinearMap.adjoint_inner_left S (σ g⁻¹ w) v).symm
      _ = ⟪σ g (ContinuousLinearMap.adjoint S v), σ g (σ g⁻¹ w)⟫ := by
          rw [(σ g).inner_map_map]
      _ = ⟪σ g (ContinuousLinearMap.adjoint S v), w⟫ := by rw [hcancel']
  have hS0 : S = 0 := by
    by_contra hne
    obtain ⟨y, hy0, hy⟩ := exists_eigenvector_adjoint_comp_self S hScomp hne
    have hcne : ‖S‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
    set B : K →L[ℝ] K := ContinuousLinearMap.adjoint S ∘L S with hB
    have hBcomp : IsCompactOperator B := hScomp.clm_comp (ContinuousLinearMap.adjoint S)
    set W : Submodule ℝ K := LinearMap.ker ((B : K →ₗ[ℝ] K) - (‖S‖ ^ 2) • LinearMap.id)
      with hW
    have hWfd : FiniteDimensional ℝ W := finiteDimensional_eigenspace B hBcomp hcne
    have hmemW : ∀ v : K, v ∈ W ↔ ContinuousLinearMap.adjoint S (S v) = ‖S‖ ^ 2 • v :=
      fun v ↦ by simp [hW, hB, sub_eq_zero]
    have hWinv : IsInvariant σ W := by
      intro g v hv
      rw [hmemW] at hv ⊢
      rw [hScomm, hSadjcomm, hv, map_smul]
    have hyM : y ∈ M :=
      N.le_topologicalClosure
        (Submodule.mem_iSup_of_mem (⟨W, hWfd, hWinv⟩ : ι) ((hmemW y).2 hy))
    have hyMo : y ∈ Mᗮ := by
      have hyeq : y = (‖S‖ ^ 2)⁻¹ • ContinuousLinearMap.adjoint S (S y) := by
        rw [hy, inv_smul_smul₀ hcne]
      rw [hyeq]
      exact Mᗮ.smul_mem _ (hSadjM _)
    have hbot : y ∈ M ⊓ Mᗮ := ⟨hyM, hyMo⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hbot
    exact hy0 hbot
  have hTx : T x = T (P x) := by
    have h0 : S x = 0 := by simp [hS0]
    rw [hSapply, map_sub, sub_eq_zero] at h0
    exact h0
  rw [hTx]
  exact hMfix _ (hMT _ (hPmem x))

end GroupApproximation.Full.A2Kirchberg.CompactExtraction
