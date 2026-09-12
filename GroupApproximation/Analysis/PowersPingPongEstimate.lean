import GroupApproximation.Analysis.PowersAveragingFromPartition
import GroupApproximation.Algebra.PingPongTranslates

/-!
# The ping-pong estimate for sums of translations

For elements `t₀, …, t_{n-1}` of a group `G` and subsets `Aᵢ`, `Bᵢ` of `G` with the
`Aᵢ` pairwise disjoint, the `Bᵢ` pairwise disjoint, and `tᵢ • (G ∖ Aᵢ) ⊆ Bᵢ`,

    ‖ λ(t₀) + ⋯ + λ(t_{n-1}) ‖ ≤ 2√n     on ℓ²(G),

so the average of the `λ(tᵢ)` has norm at most `2/√n`.

## The argument

`λ(t) P_{Aᶜ} = P_{t Aᶜ} λ(t)`, and `t Aᶜ ⊆ B` gives `λ(t) P_{Aᶜ} = P_B λ(t) P_{Aᶜ}`
(`leftRegularOperator_mul_subsetProjection_compl`).  So

    λ(tᵢ) = λ(tᵢ) P_{Aᵢ} + P_{Bᵢ} (λ(tᵢ) P_{Aᵢᶜ}),

and both sums `∑ᵢ λ(tᵢ) P_{Aᵢ}` and `∑ᵢ P_{Bᵢ} (λ(tᵢ) P_{Aᵢᶜ})` run against pairwise
orthogonal projections, hence have norm at most `√n`
(`ShulmanFill.norm_sum_mul_projection_le` and its mirror).

## Where it is used

`Analysis/ConjugateAveragingCriterion` applies it to the conjugates
`gᵢ f gᵢ⁻¹` of a nontrivial `f`: averaging `λ(f)` by `λ(g₀), …, λ(g_{n-1})` is the
average of the `λ(gᵢ f gᵢ⁻¹)`, so a ping-pong family of conjugates drives the
average of `λ(f)` to norm at most `2/√n`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

open GroupApproximation.GroupVonNeumann
open scoped Pointwise

universe u

noncomputable section

variable (G : Type u) [Group G]

/-- **`P_S + P_{Sᶜ} = 1`.** -/
theorem subsetProjection_add_compl (S : Set G) :
    subsetProjection G S + subsetProjection G Sᶜ = 1 :=
  subsetProjection_add_of_partition G disjoint_compl_right (Set.union_compl_self S)

/-- **`t • Aᶜ ⊆ B` gives `λ(t) P_{Aᶜ} = P_B λ(t) P_{Aᶜ}`.** -/
theorem leftRegularOperator_mul_subsetProjection_compl {t : G} {A B : Set G}
    (h : t • Aᶜ ⊆ B) :
    leftRegularOperator G t * subsetProjection G Aᶜ
      = subsetProjection G B * (leftRegularOperator G t * subsetProjection G Aᶜ) := by
  rw [leftRegularOperator_mul_subsetProjection, ← mul_assoc, subsetProjection_mul,
    Set.inter_eq_right.mpr h]

/-- **The ping-pong estimate**: `‖∑ᵢ λ(tᵢ)‖ ≤ 2√n`. -/
theorem norm_sum_leftRegularOperator_le_of_pingPong {n : ℕ} (t : Fin n → G)
    (A B : Fin n → Set G)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hmap : ∀ i, t i • (A i)ᶜ ⊆ B i) :
    ‖∑ i : Fin n, leftRegularOperator G (t i)‖ ≤ 2 * Real.sqrt n := by
  have hsplit : ∀ i, leftRegularOperator G (t i)
      = leftRegularOperator G (t i) * subsetProjection G (A i)
        + subsetProjection G (B i) *
          (leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ) := by
    intro i
    rw [← leftRegularOperator_mul_subsetProjection_compl G (hmap i), ← mul_add,
      subsetProjection_add_compl, mul_one]
  have hsum : ∑ i : Fin n, leftRegularOperator G (t i)
      = (∑ i : Fin n, leftRegularOperator G (t i) * subsetProjection G (A i))
        + ∑ i : Fin n, subsetProjection G (B i) *
            (leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hsplit i
  have h1 : ‖∑ i : Fin n, leftRegularOperator G (t i) * subsetProjection G (A i)‖
      ≤ Real.sqrt n * 1 :=
    ShulmanFill.norm_sum_mul_projection_le (fun i ↦ leftRegularOperator G (t i))
      (fun i ↦ subsetProjection G (A i)) 1 zero_le_one
      (fun i ↦ norm_leftRegularOperator_le_one G (t i))
      (fun i ↦ norm_subsetProjection_le_one G (A i))
      (fun i ↦ subsetProjection_star G (A i))
      (fun i j hij ↦ subsetProjection_mul_of_disjoint G (hA i j hij))
  have hb : ∀ i, ‖leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ‖ ≤ 1 := by
    intro i
    calc ‖leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ‖
        ≤ ‖leftRegularOperator G (t i)‖ * ‖subsetProjection G (A i)ᶜ‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_leftRegularOperator_le_one G (t i))
          (norm_subsetProjection_le_one G _) (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  have h2 : ‖∑ i : Fin n, subsetProjection G (B i) *
        (leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ)‖ ≤ Real.sqrt n * 1 :=
    ShulmanFill.norm_sum_projection_mul_le
      (fun i ↦ leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ)
      (fun i ↦ subsetProjection G (B i)) 1 zero_le_one hb
      (fun i ↦ norm_subsetProjection_le_one G (B i))
      (fun i ↦ subsetProjection_star G (B i))
      (fun i j hij ↦ subsetProjection_mul_of_disjoint G (hB i j hij))
  rw [hsum]
  calc ‖(∑ i : Fin n, leftRegularOperator G (t i) * subsetProjection G (A i))
        + ∑ i : Fin n, subsetProjection G (B i) *
            (leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ)‖
      ≤ ‖∑ i : Fin n, leftRegularOperator G (t i) * subsetProjection G (A i)‖
        + ‖∑ i : Fin n, subsetProjection G (B i) *
            (leftRegularOperator G (t i) * subsetProjection G (A i)ᶜ)‖ := norm_add_le _ _
    _ ≤ Real.sqrt n * 1 + Real.sqrt n * 1 := add_le_add h1 h2
    _ = 2 * Real.sqrt n := by ring

/-- **The averaged ping-pong estimate** on `ℓ²(G)`: `‖n⁻¹ ∑ᵢ λ(tᵢ)‖ ≤ 2/√n`. -/
theorem norm_average_leftRegularOperator_le_of_pingPong {n : ℕ} (hn : 0 < n)
    (t : Fin n → G) (A B : Fin n → Set G)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hmap : ∀ i, t i • (A i)ᶜ ⊆ B i) :
    ‖(n : ℂ)⁻¹ • ∑ i : Fin n, leftRegularOperator G (t i)‖ ≤ 2 / Real.sqrt n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖∑ i : Fin n, leftRegularOperator G (t i)‖
      ≤ (n : ℝ)⁻¹ * (2 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left
          (norm_sum_leftRegularOperator_le_of_pingPong G t A B hA hB hmap)
          (le_of_lt (inv_pos.mpr hnpos))
    _ = 2 * (Real.sqrt n / n) := by ring
    _ = 2 * (1 / Real.sqrt n) := by rw [Real.sqrt_div_self']
    _ = 2 / Real.sqrt n := by ring

/-- The average of reduced translations, computed in `B(ℓ²G)`. -/
theorem coe_average_reducedLeftRegular {n : ℕ} (t : Fin n → G) :
    (((n : ℂ)⁻¹ • ∑ i : Fin n, reducedLeftRegular G (t i) : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G)
      = (n : ℂ)⁻¹ • ∑ i : Fin n, leftRegularOperator G (t i) := by
  show (reducedGroupCStarSubalgebra G).subtype
      ((n : ℂ)⁻¹ • ∑ i : Fin n, reducedLeftRegular G (t i)) = _
  rw [map_smul, map_sum]
  rfl

/-- **The averaged ping-pong estimate inside `C*_r(G)`.** -/
theorem norm_average_reducedLeftRegular_le_of_pingPong {n : ℕ} (hn : 0 < n)
    (t : Fin n → G) (A B : Fin n → Set G)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hmap : ∀ i, t i • (A i)ᶜ ⊆ B i) :
    ‖(n : ℂ)⁻¹ • ∑ i : Fin n, reducedLeftRegular G (t i)‖ ≤ 2 / Real.sqrt n := by
  have h := norm_average_leftRegularOperator_le_of_pingPong G hn t A B hA hB hmap
  rw [← coe_average_reducedLeftRegular, norm_coe_reducedGroupCStar] at h
  exact h

/-- **The averaged estimate for a ping-pong family.** -/
theorem norm_average_reducedLeftRegular_le_of_isPingPongFamily {n : ℕ} (hn : 0 < n)
    {t : Fin n → G} (h : PingPongTranslates.IsPingPongFamily t) :
    ‖(n : ℂ)⁻¹ • ∑ i : Fin n, reducedLeftRegular G (t i)‖ ≤ 2 / Real.sqrt n := by
  unfold PingPongTranslates.IsPingPongFamily PingPongTranslates.IsPingPongOn at h
  obtain ⟨A, B, hA, hB, hmap⟩ := h
  exact norm_average_reducedLeftRegular_le_of_pingPong G hn t A B hA hB hmap

end

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms subsetProjection_add_compl
#audit_axioms leftRegularOperator_mul_subsetProjection_compl
#audit_axioms norm_sum_leftRegularOperator_le_of_pingPong
#audit_axioms norm_average_leftRegularOperator_le_of_pingPong
#audit_axioms coe_average_reducedLeftRegular
#audit_axioms norm_average_reducedLeftRegular_le_of_pingPong
#audit_axioms norm_average_reducedLeftRegular_le_of_isPingPongFamily
