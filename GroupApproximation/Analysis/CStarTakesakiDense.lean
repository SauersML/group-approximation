import GroupApproximation.Analysis.CStarTakesakiCoefficient
import GroupApproximation.Analysis.CStarMinTensorNorm

/-!
# Coefficient vectors are dense: the approximation layer of Takesaki's lane

## What this module provides

The coefficient calculus of `CStarTakesakiCoefficient` computes quadratic
forms of a product representation at *coefficient vectors*
`Σⱼ π(aⱼ)ζ ⊗ ηⱼ`.  To turn those computations into operator-norm bounds the
coefficient vectors must exhaust a dense subspace of the algebraic tensor
product of the representation spaces.  This module proves exactly that, for
the GNS representations of states:

* `gnsRep_apply_gnsVector` --- the GNS representation applied to the cyclic
  vector is the canonical image of the algebra element: `π_φ(u)Ω = [u]`.
  (This is the identity inside `CStarStateGNS`'s norm computation, extracted
  and named, because the density of `{π_φ(u)Ω}` in the GNS space *is* the
  density of the canonical image, which is density of a completion's core.)
* `inner_gnsVector_gnsRep` --- the diagonal matrix coefficient of the cyclic
  vector computes the state: `⟪Ω, π_φ(u)Ω⟫ = φ(u)`.
* `exists_fin_sum_tmul` --- every element of an algebraic tensor product is
  a finite sum of elementary tensors, with `Fin`-indexed witnesses.
* `dense_span_tmul_left` / `dense_span_tmul_right` --- the span of the
  elementary tensors whose left (resp. right) leg comes from a dense subset
  is dense in the inner-product norm of the algebraic tensor product.  The
  proof is quantitative: approximate each leg within
  `ε / (n * (‖other leg‖ + 1))` and add up.
* `gnsCoeffSpan` / `rightGnsCoeffSpan`, with their normal-form extractions
  (`exists_coeffVector_of_mem_gnsCoeffSpan`,
  `exists_rightCoeffVector_of_mem`) and density
  (`dense_gnsCoeffSpan`, `dense_rightGnsCoeffSpan`).

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  Consumed by
`CStarTakesakiMinLe.lean`.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped InnerProductSpace TensorProduct

universe u v w x

/-! ## Finite representations of tensors -/

section FinRep

variable {E : Type u} {F : Type v} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

/-- Every element of the algebraic tensor product is a finite sum of
elementary tensors, with `Fin`-indexed witnesses. -/
theorem exists_fin_sum_tmul (w : E ⊗[ℂ] F) :
    ∃ (n : ℕ) (v : Fin n → E) (k : Fin n → F),
      w = ∑ i : Fin n, v i ⊗ₜ[ℂ] k i := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul e f => exact ⟨1, fun _ => e, fun _ => f, by simp⟩
  | add y z hy hz =>
      obtain ⟨n₁, v₁, k₁, rfl⟩ := hy
      obtain ⟨n₂, v₂, k₂, rfl⟩ := hz
      refine ⟨n₁ + n₂, Fin.append v₁ v₂, Fin.append k₁ k₂, ?_⟩
      rw [Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.append_left, Fin.append_left]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.append_right, Fin.append_right]

end FinRep

/-! ## Density of spans of one-sided-dense elementary tensors -/

section DenseSpan

variable {E : Type u} {F : Type v} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Density on the left leg.**  If `D ⊆ E` is dense, the span of the
elementary tensors with left leg in `D` is dense in `E ⊗[ℂ] F` for the
inner-product norm. -/
theorem dense_span_tmul_left {D : Set E} (hD : Dense D) :
    Dense ((Submodule.span ℂ
      {w : E ⊗[ℂ] F | ∃ v ∈ D, ∃ k : F, w = v ⊗ₜ[ℂ] k} : Submodule ℂ _) :
        Set (E ⊗[ℂ] F)) := by
  intro w
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, v, k, rfl⟩ := exists_fin_sum_tmul w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simpa using hε
  · have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    -- choose approximants
    have hchoice : ∀ i : Fin n, ∃ d ∈ D,
        dist (v i) d < ε / (n * (‖k i‖ + 1)) := by
      intro i
      have hpos : 0 < ε / (n * (‖k i‖ + 1)) := by positivity
      have h := hD.exists_dist_lt (v i) hpos
      obtain ⟨d, hd, hdist⟩ := h
      exact ⟨d, hd, hdist⟩
    choose d hdD hdist using hchoice
    refine ⟨∑ i : Fin n, d i ⊗ₜ[ℂ] k i, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ =>
        Submodule.subset_span ⟨d i, hdD i, k i, rfl⟩
    · have hsub : (∑ i : Fin n, v i ⊗ₜ[ℂ] k i)
          - (∑ i : Fin n, d i ⊗ₜ[ℂ] k i)
          = ∑ i : Fin n, (v i - d i) ⊗ₜ[ℂ] k i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.sub_tmul]
      have hle : dist (∑ i : Fin n, v i ⊗ₜ[ℂ] k i)
          (∑ i : Fin n, d i ⊗ₜ[ℂ] k i)
          ≤ ∑ i : Fin n, ‖v i - d i‖ * ‖k i‖ := by
        rw [dist_eq_norm, hsub]
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [TensorProduct.norm_tmul]
      have hstrict : ∑ i : Fin n, ‖v i - d i‖ * ‖k i‖ < ε := by
        have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            ‖v i - d i‖ * ‖k i‖ < ε / n := by
          intro i _
          have h1 : ‖v i - d i‖ < ε / (n * (‖k i‖ + 1)) := by
            rw [← dist_eq_norm]
            exact hdist i
          have hk1 : (0 : ℝ) < ‖k i‖ + 1 := by positivity
          have hδ : (0 : ℝ) < ε / (n * (‖k i‖ + 1)) := by positivity
          have h2 : ‖v i - d i‖ * ‖k i‖
              ≤ (ε / (n * (‖k i‖ + 1))) * ‖k i‖ :=
            mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
          have h3 : (ε / (n * (‖k i‖ + 1))) * ‖k i‖
              < (ε / (n * (‖k i‖ + 1))) * (‖k i‖ + 1) :=
            mul_lt_mul_of_pos_left (lt_add_one _) hδ
          have h4 : (ε / (n * (‖k i‖ + 1))) * (‖k i‖ + 1) = ε / n := by
            field_simp
            try ring
          linarith
        have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
          rw [Finset.univ_nonempty_iff]
          exact Fin.pos_iff_nonempty.mp hn
        have h5 := Finset.sum_lt_sum_of_nonempty hne hterm
        have h6 : ∑ _i : Fin n, ε / (n : ℝ) = ε := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_div_cancel₀ _ hn0]
        linarith
      exact lt_of_le_of_lt hle hstrict

/-- **Density on the right leg.**  Mirror of `dense_span_tmul_left`. -/
theorem dense_span_tmul_right {D : Set F} (hD : Dense D) :
    Dense ((Submodule.span ℂ
      {w : E ⊗[ℂ] F | ∃ v ∈ D, ∃ h : E, w = h ⊗ₜ[ℂ] v} : Submodule ℂ _) :
        Set (E ⊗[ℂ] F)) := by
  intro w
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, v, k, rfl⟩ := exists_fin_sum_tmul w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simpa using hε
  · have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hchoice : ∀ i : Fin n, ∃ d ∈ D,
        dist (k i) d < ε / (n * (‖v i‖ + 1)) := by
      intro i
      have hpos : 0 < ε / (n * (‖v i‖ + 1)) := by positivity
      obtain ⟨d, hd, hdist⟩ := hD.exists_dist_lt (k i) hpos
      exact ⟨d, hd, hdist⟩
    choose d hdD hdist using hchoice
    refine ⟨∑ i : Fin n, v i ⊗ₜ[ℂ] d i, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ =>
        Submodule.subset_span ⟨d i, hdD i, v i, rfl⟩
    · have hsub : (∑ i : Fin n, v i ⊗ₜ[ℂ] k i)
          - (∑ i : Fin n, v i ⊗ₜ[ℂ] d i)
          = ∑ i : Fin n, v i ⊗ₜ[ℂ] (k i - d i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.tmul_sub]
      have hle : dist (∑ i : Fin n, v i ⊗ₜ[ℂ] k i)
          (∑ i : Fin n, v i ⊗ₜ[ℂ] d i)
          ≤ ∑ i : Fin n, ‖v i‖ * ‖k i - d i‖ := by
        rw [dist_eq_norm, hsub]
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [TensorProduct.norm_tmul]
      have hstrict : ∑ i : Fin n, ‖v i‖ * ‖k i - d i‖ < ε := by
        have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            ‖v i‖ * ‖k i - d i‖ < ε / n := by
          intro i _
          have h1 : ‖k i - d i‖ < ε / (n * (‖v i‖ + 1)) := by
            rw [← dist_eq_norm]
            exact hdist i
          have hδ : (0 : ℝ) < ε / (n * (‖v i‖ + 1)) := by positivity
          have h2 : ‖v i‖ * ‖k i - d i‖
              ≤ ‖v i‖ * (ε / (n * (‖v i‖ + 1))) :=
            mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
          have h3 : ‖v i‖ * (ε / (n * (‖v i‖ + 1)))
              < (‖v i‖ + 1) * (ε / (n * (‖v i‖ + 1))) :=
            mul_lt_mul_of_pos_right (lt_add_one _) hδ
          have h4 : (‖v i‖ + 1) * (ε / (n * (‖v i‖ + 1))) = ε / n := by
            field_simp
            try ring
          linarith
        have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
          rw [Finset.univ_nonempty_iff]
          exact Fin.pos_iff_nonempty.mp hn
        have h5 := Finset.sum_lt_sum_of_nonempty hne hterm
        have h6 : ∑ _i : Fin n, ε / (n : ℝ) = ε := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_div_cancel₀ _ hn0]
        linarith
      exact lt_of_le_of_lt hle hstrict

end DenseSpan

/-! ## The GNS vector identities -/

section GNSVector

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

attribute [local instance] CStarState.instSpectralOrder
  CStarState.instSpectralStarOrdered

/-- **The GNS representation moves the cyclic vector to the canonical
image**: `π_φ(u) Ω = [u]`.  Extracted from the norm computation in
`CStarStateGNS`, because the density of `{π_φ(u) Ω : u ∈ A}` in the GNS
space is exactly the density of the completion's core. -/
theorem gnsRep_apply_gnsVector (φ : State A) (u : A) :
    (φ.gnsRep).hom u φ.gnsVector
      = ((φ.toPositive.toPreGNS u : φ.toPositive.PreGNS) :
          φ.toPositive.GNS) := by
  show (φ.toPositive.leftMulMapPreGNS u).completion
      ((φ.toPositive.toPreGNS 1 : φ.toPositive.PreGNS) :
        φ.toPositive.GNS) = _
  rw [ContinuousLinearMap.completion_apply_coe]
  congr 1
  show φ.toPositive.toPreGNS
      (u * φ.toPositive.ofPreGNS (φ.toPositive.toPreGNS 1))
    = φ.toPositive.toPreGNS u
  rw [PositiveLinearMap.ofPreGNS_toPreGNS, mul_one]

/-- **The diagonal matrix coefficient of the cyclic vector computes the
state**: `⟪Ω, π_φ(u) Ω⟫ = φ(u)`. -/
theorem inner_gnsVector_gnsRep (φ : State A) (u : A) :
    ⟪φ.gnsVector, (φ.gnsRep).hom u φ.gnsVector⟫_ℂ = φ.toCLM u := by
  rw [gnsRep_apply_gnsVector]
  show ⟪((φ.toPositive.toPreGNS 1 : φ.toPositive.PreGNS) :
      φ.toPositive.GNS),
    ((φ.toPositive.toPreGNS u : φ.toPositive.PreGNS) :
      φ.toPositive.GNS)⟫_ℂ = φ.toCLM u
  rw [UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul,
    State.toPositive_apply]

/-- The orbit of the cyclic vector under the GNS representation is dense in
the GNS space: it is the canonical image of the algebra, the completion's
core. -/
theorem dense_range_gnsRep_gnsVector (φ : State A) :
    Dense (Set.range fun u : A => (φ.gnsRep).hom u φ.gnsVector) := by
  intro v
  have hv : v ∈ closure (Set.range
      ((↑) : φ.toPositive.PreGNS → φ.toPositive.GNS)) :=
    UniformSpace.Completion.denseRange_coe v
  have hr : Set.range ((↑) : φ.toPositive.PreGNS → φ.toPositive.GNS)
      ⊆ Set.range (fun u : A => (φ.gnsRep).hom u φ.gnsVector) := by
    rintro _ ⟨p, rfl⟩
    refine ⟨φ.toPositive.ofPreGNS p, ?_⟩
    rw [gnsRep_apply_gnsVector, PositiveLinearMap.toPreGNS_ofPreGNS]
  exact closure_mono hr hv

end GNSVector

/-! ## The GNS coefficient spans -/

section CoeffSpan

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- The span of the elementary tensors whose left leg is in the orbit of
the GNS cyclic vector. -/
noncomputable def gnsCoeffSpan (φ : State A) (K : Type x)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :
    Submodule ℂ (φ.GNSSpace ⊗[ℂ] K) :=
  Submodule.span ℂ
    {w : φ.GNSSpace ⊗[ℂ] K |
      ∃ v ∈ Set.range fun u : A => (φ.gnsRep).hom u φ.gnsVector,
        ∃ k : K, w = v ⊗ₜ[ℂ] k}

theorem dense_gnsCoeffSpan (φ : State A) {K : Type x}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :
    Dense ((gnsCoeffSpan φ K : Submodule ℂ (φ.GNSSpace ⊗[ℂ] K)) :
      Set (φ.GNSSpace ⊗[ℂ] K)) :=
  dense_span_tmul_left (dense_range_gnsRep_gnsVector φ)

/-- **Normal form**: every element of the coefficient span is a coefficient
vector of the GNS representation at the cyclic vector. -/
theorem exists_coeffVector_of_mem_gnsCoeffSpan (φ : State A)
    {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {w : φ.GNSSpace ⊗[ℂ] K} (hw : w ∈ gnsCoeffSpan φ K) :
    ∃ (n : ℕ) (a : Fin n → A) (η : Fin n → K),
      w = coeffVector φ.gnsRep φ.gnsVector a η := by
  induction hw using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨v, ⟨u, rfl⟩, k, rfl⟩ := ht
      exact ⟨1, fun _ => u, fun _ => k, by simp [coeffVector]⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp [coeffVector]⟩
  | add y z hy hz ihy ihz =>
      obtain ⟨n₁, a₁, η₁, rfl⟩ := ihy
      obtain ⟨n₂, a₂, η₂, rfl⟩ := ihz
      refine ⟨n₁ + n₂, Fin.append a₁ a₂, Fin.append η₁ η₂, ?_⟩
      simp only [coeffVector]
      rw [Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.append_left, Fin.append_left]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.append_right, Fin.append_right]
  | smul z y hy ihy =>
      obtain ⟨n, a, η, rfl⟩ := ihy
      refine ⟨n, fun j => z • a j, η, ?_⟩
      simp only [coeffVector]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_smul, smul_apply,
        TensorProduct.smul_tmul']

end CoeffSpan

section RightCoeffSpan

variable {B : Type v} [CStarAlgebra B] [Nontrivial B]

/-- The span of the elementary tensors whose right leg is in the orbit of
the GNS cyclic vector. -/
noncomputable def rightGnsCoeffSpan (ψ : State B) (H : Type w)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Submodule ℂ (H ⊗[ℂ] ψ.GNSSpace) :=
  Submodule.span ℂ
    {w : H ⊗[ℂ] ψ.GNSSpace |
      ∃ v ∈ Set.range fun b : B => (ψ.gnsRep).hom b ψ.gnsVector,
        ∃ h : H, w = h ⊗ₜ[ℂ] v}

theorem dense_rightGnsCoeffSpan (ψ : State B) {H : Type w}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Dense ((rightGnsCoeffSpan ψ H :
        Submodule ℂ (H ⊗[ℂ] ψ.GNSSpace)) : Set (H ⊗[ℂ] ψ.GNSSpace)) :=
  dense_span_tmul_right (dense_range_gnsRep_gnsVector ψ)

/-- **Normal form** for the mirrored span: every element is a mirrored
coefficient vector of the GNS representation at the cyclic vector. -/
theorem exists_rightCoeffVector_of_mem (ψ : State B)
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {w : H ⊗[ℂ] ψ.GNSSpace} (hw : w ∈ rightGnsCoeffSpan ψ H) :
    ∃ (n : ℕ) (b : Fin n → B) (ξ : Fin n → H),
      w = rightCoeffVector ψ.gnsRep ψ.gnsVector b ξ := by
  induction hw using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨v, ⟨b, rfl⟩, h, rfl⟩ := ht
      exact ⟨1, fun _ => b, fun _ => h, by simp [rightCoeffVector]⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp [rightCoeffVector]⟩
  | add y z hy hz ihy ihz =>
      obtain ⟨n₁, b₁, ξ₁, rfl⟩ := ihy
      obtain ⟨n₂, b₂, ξ₂, rfl⟩ := ihz
      refine ⟨n₁ + n₂, Fin.append b₁ b₂, Fin.append ξ₁ ξ₂, ?_⟩
      simp only [rightCoeffVector]
      rw [Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.append_left, Fin.append_left]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.append_right, Fin.append_right]
  | smul z y hy ihy =>
      obtain ⟨n, b, ξ, rfl⟩ := ihy
      refine ⟨n, fun j => z • b j, ξ, ?_⟩
      simp only [rightCoeffVector]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_smul, smul_apply,
        TensorProduct.tmul_smul]

end RightCoeffSpan

end CStarTensor
end GroupApproximation
