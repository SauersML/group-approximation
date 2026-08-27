import GroupApproximation.PropertyTT.Basic

/-!
# Kazhdan globalization for relative `(TT)/T`

This file formalizes the elementary Hilbert-space argument underlying
Mimura's globalization criterion (Theorem 8.1.7 of his thesis).  The proof is
included: a quasi-cocycle bounded on a generating set normalized by `H`
makes each vector `b(h)` uniformly almost invariant; a Kazhdan pair then
bounds `b(h)` uniformly.  Thus no external rigidity theorem is represented by
an axiom or a premise.
-/

namespace GroupApproximation

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]

/-- **Kazhdan relative globalization.**  If `G` has property `(T)`, `S`
generates `G`, `H` normalizes `S`, and quasi-cocycles without invariant
vectors are bounded on `S`, then they are bounded on `H`.

The quantitative proof uses the sum of the lengths of fixed `S ∪ S⁻¹` words
for a finite Kazhdan set. -/
theorem hasRelativeTTmodT_of_kazhdan_of_normalized_set
    (H : Subgroup G) (S : Set G)
    (hT : HasKazhdanPropertyT.{u, v} G)
    (hgen : Subgroup.closure S = ⊤)
    (hnormalizes : ∀ h : G, h ∈ H → ∀ s ∈ S, h⁻¹ * s * h ∈ S)
    (hrelS : HasRelativeTTmodTOnSet.{u, v} G S) :
    HasRelativeTTmodT.{u, v} G H := by
  intro E _ _ _ rho hno b D hb
  obtain ⟨K, ε, hK⟩ := hT
  have hKc : IsKazhdanPairComplex.{u, v} G K ε := hK.toComplex
  obtain ⟨C, hC, hbound⟩ := hrelS E rho hno b D hb
  have hwords : ∀ g : G, ∃ l : List G,
      (∀ x ∈ l, x ∈ symmetrized S) ∧ l.prod = g := by
    intro g
    apply exists_list_of_mem_closure
    rw [hgen]
    exact Subgroup.mem_top g
  choose word hword hprod using hwords
  let L : ℕ := ∑ k ∈ K, (word k).length
  let A : ℝ := 2 * C + 2 * D
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (mul_nonneg (by norm_num) hC)
      (mul_nonneg (by norm_num) hb.1)
  refine ⟨(L : ℝ) * A / ε, div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) hA) hKc.1.le, ?_⟩
  intro h hh
  by_cases hbh : b h = 0
  · rw [hbh, norm_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) hKc.1.le
  obtain ⟨k, hk, hkmove⟩ :=
    hKc.exists_moved_mul_norm_of_noInvariant rho hno (b h) hbh
  have hletter : ∀ x ∈ word k, ‖rho x (b h) - b h‖ ≤ A := by
    intro x hx
    rcases hword k x hx with hxS | hxinvS
    · exact quasiCocycle_displacement_le_of_normalizes hb hxS
        (hnormalizes h hh x hxS) hbound
    · rw [← norm_unitary_inv_sub rho x (b h)]
      exact quasiCocycle_displacement_le_of_normalizes hb hxinvS
        (hnormalizes h hh x⁻¹ hxinvS) hbound
  have hkdisp : ‖rho k (b h) - b h‖ ≤ ((word k).length : ℝ) * A := by
    have hworddisp := norm_unitary_prod_sub_le rho (b h) (word k) hletter
    rw [hprod k] at hworddisp
    exact hworddisp
  have hlen : (word k).length ≤ L := by
    dsimp [L]
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (word j).length) hk
  have hlenReal : ((word k).length : ℝ) ≤ L := by
    exact_mod_cast hlen
  have hwidth : ((word k).length : ℝ) * A ≤ (L : ℝ) * A :=
    mul_le_mul_of_nonneg_right hlenReal hA
  have hmain : ε * ‖b h‖ ≤ (L : ℝ) * A :=
    hkmove.trans (hkdisp.trans hwidth)
  exact (le_div_iff₀ hKc.1).2 (by simpa [mul_comm] using hmain)

/-- The complete abstract criterion: the normalized-set argument first
produces relative `(TT)/T` for `H`, and a finite cover by fixed conjugates of
`H` plus bounded product width makes the conclusion global. -/
theorem hasTTmodT_of_kazhdan_normalized_set_of_bounded_conjugates
    (H : Subgroup G) (Q : Set G)
    (hT : HasKazhdanPropertyT.{u, v} G)
    (hgen : Subgroup.closure Q = ⊤)
    (hnormalizes : ∀ h : G, h ∈ H → ∀ q ∈ Q, h⁻¹ * q * h ∈ Q)
    (hrelQ : HasRelativeTTmodTOnSet.{u, v} G Q)
    (conjugators : Finset G) (S : Set G) (N : ℕ)
    (hcover : ∀ x ∈ S, ∃ a ∈ conjugators,
      ∃ h : G, h ∈ H ∧ x = a * h * a⁻¹)
    (hprod : IsBoundedProduct G S N) : HasTTmodT.{u, v} G :=
  hasTTmodT_of_relative_of_bounded_conjugates H
    (hasRelativeTTmodT_of_kazhdan_of_normalized_set H Q hT hgen
      hnormalizes hrelQ)
    conjugators S N hcover hprod

end GroupApproximation
