import GroupApproximation.Analysis.PowersPingPongEstimate
import GroupApproximation.Analysis.PowersAveragingFromPowersProperty
import GroupApproximation.Analysis.PowersAveragingComposition
import GroupApproximation.Algebra.NaiveFreeProductPingPong

/-!
# Powers' averaging estimate from averaging translations

`PowersAveragingEstimate G` asks that every element of `C*_r(G)` with vanishing
canonical trace can be averaged, by the canonical unitaries of finitely many group
elements, to arbitrarily small norm.  This module proves it from a condition on
**single translations**:

> `ConjugateAveragingCriterion G`: for every finite `F ⊆ G ∖ {1}` and `ε > 0` there
> are `g₀, …, g_{n-1}` with `‖n⁻¹ ∑ᵢ λ(gᵢ f gᵢ⁻¹)‖ ≤ ε` for every `f ∈ F`.

This is the direction of Haagerup's characterization of C⋆-simplicity that the
argument needs, and it is elementary: approximate the element by a finite
combination `∑ⱼ cⱼ λ(γⱼ)`, delete the identity coefficient (it is small because
the trace vanishes), and average: `λ(g) λ(γ) λ(g)⋆ = λ(g γ g⁻¹)`, so the average of
the combination is `∑ⱼ cⱼ` times the averages of the `λ(γⱼ)`, each of norm at most
`ε`.  Averaging is a contraction, which carries the estimate from the approximant
to the element.

Then:

* `conjugateAveragingCriterion_of_pingPongConjugateProperty` — ping-pong families
  of conjugates give the criterion, through the `2/√n` estimate of
  `Analysis/PowersPingPongEstimate`;
* `powersAveragingEstimate_of_naiveFreeProductProperty` — property `P_naive`
  (`Algebra/NaiveFreeProductProperty`) gives Powers' averaging estimate, hence
  (`Analysis/PowersAveraging`, `Analysis/PowersAveragingUniqueTrace`) simplicity
  of `C*_r(G)` and uniqueness of its tracial state.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

open GroupApproximation.GroupVonNeumann
open GroupApproximation.NaiveFreeProduct
open scoped Pointwise

universe u

noncomputable section

variable (G : Type u) [Group G]

/-- **The averaging criterion for single translations.**  For every finite
`F ⊆ G ∖ {1}` and every `ε > 0` there are `g₀, …, g_{n-1}` such that the average of
the translations by the conjugates `gᵢ f gᵢ⁻¹` has norm at most `ε`, for every
`f ∈ F` at once. -/
def ConjugateAveragingCriterion : Prop :=
  ∀ F : Finset G, (1 : G) ∉ F → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (g : Fin n → G), 0 < n ∧
      ∀ f ∈ F, ‖(n : ℂ)⁻¹ • ∑ i : Fin n, reducedLeftRegular G (g i * f * (g i)⁻¹)‖ ≤ ε

set_option maxHeartbeats 1000000 in
/-- **Powers' averaging estimate from the averaging criterion.** -/
theorem powersAveragingEstimate_of_conjugateAveragingCriterion
    (h : ConjugateAveragingCriterion G) : PowersAveragingEstimate G := by
  classical
  intro a hτa ε hε
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  -- Approximate `a` by a finite combination of translations.
  obtain ⟨m, c, γ, happrox⟩ := exists_translationSum_approx G a.2 hδ
  set b : ReducedGroupCStar G := ∑ j : Fin m, c j • reducedLeftRegular G (γ j) with hbdef
  have hbcoe : (b : GroupHilbert G →L[ℂ] GroupHilbert G)
      = ∑ j : Fin m, c j • leftRegularOperator G (γ j) := by
    rw [hbdef]
    exact coe_translationSum G c γ
  have hab : ‖a - b‖ < δ := by
    have hsub : ((a - b : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G)
        = (a : GroupHilbert G →L[ℂ] GroupHilbert G)
          - ∑ j : Fin m, c j • leftRegularOperator G (γ j) := by
      have hmap := map_sub (reducedInclusion G) a b
      rw [reducedInclusion_apply, reducedInclusion_apply, reducedInclusion_apply,
        hbcoe] at hmap
      exact hmap
    have hnorm := happrox
    rw [← hsub, norm_coe_reducedGroupCStar] at hnorm
    exact hnorm
  -- Zero the coefficients at the identity.
  set c' : Fin m → ℂ := fun j ↦ if γ j = 1 then 0 else c j with hc'
  set b₀ : ReducedGroupCStar G := ∑ j : Fin m, c' j • reducedLeftRegular G (γ j)
    with hb₀
  set κ : ℂ := ∑ j : Fin m, (if γ j = 1 then c j else 0) with hκdef
  have hsplit : b = b₀ + κ • 1 := by
    rw [hbdef, hb₀, hκdef, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hγ : γ j = 1
    · rw [hc']
      simp [hγ]
    · simp [hc', hγ]
  have hτb : canonicalFaithfulTracialState G b = κ := by
    have hlin : canonicalCoefficientAtOne G b
        = ∑ j : Fin m,
          c j * canonicalCoefficientAtOne G (reducedLeftRegular G (γ j)) := by
      rw [hbdef, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
    show canonicalCoefficientAtOne G b = κ
    rw [hlin, hκdef]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [canonicalCoefficientAtOne_reducedLeftRegular]
    by_cases hγ : γ j = 1 <;> simp [hγ]
  have hκsmall : ‖κ‖ < δ := by
    have hbound : ‖canonicalFaithfulTracialState G (b - a)‖ ≤ ‖b - a‖ :=
      Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le
        (canonicalFaithfulTracialState G).toTracialState (b - a)
    have heq : canonicalFaithfulTracialState G (b - a) = κ := by
      rw [FaithfulTracialState.map_sub, hτa, hτb, sub_zero]
    rw [heq] at hbound
    calc ‖κ‖ ≤ ‖b - a‖ := hbound
      _ = ‖a - b‖ := by rw [← norm_neg, neg_sub]
      _ < δ := hab
  have hab₀ : ‖a - b₀‖ < 2 * δ := by
    have hdecomp : a - b₀ = (a - b) + κ • (1 : ReducedGroupCStar G) := by
      rw [hsplit]; abel
    have hsmul : ‖κ • (1 : ReducedGroupCStar G)‖ ≤ ‖κ‖ := by
      rw [norm_smul]
      nlinarith [norm_nonneg κ, norm_one_le_one G,
        norm_nonneg (1 : ReducedGroupCStar G)]
    calc ‖a - b₀‖ = ‖(a - b) + κ • (1 : ReducedGroupCStar G)‖ := by rw [hdecomp]
      _ ≤ ‖a - b‖ + ‖κ • (1 : ReducedGroupCStar G)‖ := norm_add_le _ _
      _ < δ + δ :=
          add_lt_add_of_lt_of_le hab (le_of_lt (lt_of_le_of_lt hsmul hκsmall))
      _ = 2 * δ := by ring
  -- The criterion, at the support of `b₀`.
  set F : Finset G := (Finset.univ.image γ).erase 1 with hF
  have hFne : (1 : G) ∉ F := by
    rw [hF]
    exact Finset.notMem_erase 1 _
  set S : ℝ := ∑ j : Fin m, ‖c' j‖ with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  set η : ℝ := δ / (S + 1) with hη
  have hηpos : 0 < η := by rw [hη]; exact div_pos hδ (by linarith)
  obtain ⟨n, g, hn, hsmall⟩ := h F hFne η hηpos
  -- Averaging `b₀` averages each translation.
  have havg : (n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i))
      = ∑ j : Fin m, c' j • ((n : ℂ)⁻¹ • ∑ i : Fin n,
          reducedLeftRegular G (g i * γ j * (g i)⁻¹)) := by
    have hterm : ∀ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i))
          = ∑ j : Fin m, c' j • reducedLeftRegular G (g i * γ j * (g i)⁻¹) := by
      intro i
      rw [hb₀, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_smul_comm, smul_mul_assoc, conj_reducedLeftRegular]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
  have hb₀est : ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
      reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i))‖ ≤ δ := by
    rw [havg]
    calc ‖∑ j : Fin m, c' j • ((n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (g i * γ j * (g i)⁻¹))‖
        ≤ ∑ j : Fin m, ‖c' j • ((n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (g i * γ j * (g i)⁻¹))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin m, ‖c' j‖ * η := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [norm_smul]
          by_cases hγ : γ j = 1
          · have hc : c' j = 0 := by rw [hc']; simp [hγ]
            rw [hc, norm_zero, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left (hsmall (γ j) ?_) (norm_nonneg _)
            rw [hF, Finset.mem_erase]
            exact ⟨hγ, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
      _ = S * η := by rw [hS, Finset.sum_mul]
      _ ≤ δ := by
          rw [hη, ← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith [hδ.le, hSnn]
  -- The difference is handled by the contraction bound.
  have hdiff : ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      - ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)))
      = (n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * (a - b₀) * star (reducedLeftRegular G (g i)) := by
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    simp only [mul_sub, sub_mul]
  have hdiffbound : ‖((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      - ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)))‖
      ≤ ‖a - b₀‖ := by
    rw [hdiff]
    exact norm_reducedAverage_le G (a - b₀) hn g
  refine ⟨n, g, hn, ?_⟩
  set X : ReducedGroupCStar G := (n : ℂ)⁻¹ • ∑ i : Fin n,
    reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)) with hX
  set Y : ReducedGroupCStar G := (n : ℂ)⁻¹ • ∑ i : Fin n,
    reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)) with hY
  have hXY : (X - Y) + Y = X := by abel
  calc ‖X‖ = ‖(X - Y) + Y‖ := by rw [hXY]
    _ ≤ ‖X - Y‖ + ‖Y‖ := norm_add_le _ _
    _ ≤ ‖a - b₀‖ + δ := add_le_add hdiffbound hb₀est
    _ ≤ 2 * δ + δ := by linarith [hab₀.le]
    _ ≤ ε := by rw [hδdef]; linarith

/-- **Ping-pong families of conjugates give the averaging criterion**: a ping-pong
family of `n` conjugates averages `λ(f)` to norm at most `2/√n`. -/
theorem conjugateAveragingCriterion_of_pingPongConjugateProperty
    (h : PingPongConjugateProperty G) : ConjugateAveragingCriterion G := by
  intro F hF ε hε
  set n : ℕ := ⌈(2 / ε) ^ 2⌉₊ + 1 with hn
  have hnpos : 0 < n := Nat.succ_pos _
  obtain ⟨g, hg⟩ := h F hF n hnpos
  refine ⟨n, g, hnpos, fun f hf ↦ ?_⟩
  refine le_trans (norm_average_reducedLeftRegular_le_of_isPingPongFamily G hnpos (hg f hf)) ?_
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have h2ε : 2 / ε ≤ Real.sqrt n := by
    have h1 : (2 / ε) ^ 2 ≤ (n : ℝ) := by
      have h3 : (2 / ε) ^ 2 ≤ ((⌈(2 / ε) ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h4 : ((⌈(2 / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
        rw [hn]
        exact_mod_cast Nat.le_succ _
      linarith
    have h5 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h5
  rw [div_le_iff₀ hsqrtpos]
  have h6 := (div_le_iff₀ hε).mp h2ε
  linarith [h6]

/-- **Property `P_naive` gives Powers' averaging estimate.** -/
theorem powersAveragingEstimate_of_naiveFreeProductProperty
    (h : NaiveFreeProductProperty G) : PowersAveragingEstimate G :=
  powersAveragingEstimate_of_conjugateAveragingCriterion G
    (conjugateAveragingCriterion_of_pingPongConjugateProperty G
      (pingPongConjugateProperty_of_naiveFreeProductProperty h))

end

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms ConjugateAveragingCriterion
#audit_axioms powersAveragingEstimate_of_conjugateAveragingCriterion
#audit_axioms conjugateAveragingCriterion_of_pingPongConjugateProperty
#audit_axioms powersAveragingEstimate_of_naiveFreeProductProperty
