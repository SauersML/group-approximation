import GroupApproximation.BooneHigmanLinear.LSCore.PNormal
import GroupApproximation.Meta.AxiomGuard

/-!
# Lavrenov–Sinchuk, Lemma 5.9: `P̃_α(0) ⊴ P̃_α(*)` and `P̃_α(*) = ⋃_m P̃_α(0) x_{-α}(m X)`

For `α = (i, j)` with a third index `k ∉ {i, j}`:
* `cj_gen_mem`: `y⁻¹ g y ∈ P̃_α(0)` for every generator `g` of `P̃_α(0)`, `y = x_ji(c X)`;
* `cj_mem_pZero`: the same for all `g ∈ P̃_α(0)`;
* `conj_mem_pZero`: `g h g⁻¹ ∈ P̃_α(0)` for `g ∈ P̃_α(*)`, `h ∈ P̃_α(0)` (normality);
* `mem_pStar_iff`: `g ∈ P̃_α(*) ↔ ∃ m ∈ M, ∃ g₀ ∈ P̃_α(0), g = g₀ x_ji(m X)`;
* `pAlpha_decomp`: in that decomposition `m = p_α(g)`, so `m` is unique.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (zElt polyIdeal)
open Polynomial (X C)

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [CommRing A] {M : Ideal A}

section Conj

variable {i j : I} (hij : i ≠ j) (m : A)

/-- **L–S (5.6)**: conjugating a P2 generator by `x_ji(m X)`. -/
theorem cj_P2_mem {p q : I} (hpq : p ≠ q) (hA : Acute i j p q) {f : Polynomial A}
    (hf : f ∈ polyIdeal M) (ξ : Polynomial A) :
    cj (x j i hij.symm (C m * X)) (zElt p q hpq f (X * ξ)) ∈ pZero M i j hij := by
  have hc : f * C m ∈ polyIdeal M := Ideal.mul_mem_right _ _ hf
  rcases hA with ⟨rfl, hqj⟩ | ⟨rfl, hpi⟩
  · -- β = (i, q), obtuse for (j, i)
    rw [z_conj_obtuse_row hij.symm hpq (fun h => hqj h.symm)]
    exact mul_mem (mul_mem (mem_P4 hij (neg_mem (Ideal.mul_mem_right ξ _ hc)) (by ring))
      (x_mem_P1 hij _ (adj_row_right hij (fun h => hpq h.symm)) (neg_mem hc) (by ring)))
      (mem_P2 hij hpq (Or.inl ⟨rfl, hqj⟩) hf ξ rfl)
  · -- β = (p, j), obtuse for (j, i)
    rw [z_conj_obtuse_col hij.symm hpq hpi]
    exact mul_mem (mul_mem (mem_P4 hij (neg_mem (Ideal.mul_mem_right ξ _ hc)) (by ring))
      (x_mem_P1 hij _ (adj_col_left hpq hpi) hc (by ring)))
      (mem_P2 hij hpq (Or.inr ⟨rfl, hpi⟩) hf ξ rfl)

#audit_axioms cj_P2_mem

/-- **L–S Lemma 5.9**, generators: `y⁻¹ g y ∈ P̃_α(0)` for `y = x_ji(m X)`. -/
theorem cj_gen_mem {k : I} (hki : k ≠ i) (hkj : k ≠ j) {g : SteinbergGroup I (Polynomial A)}
    (hg : g ∈ pGens M i j hij) : cj (x j i hij.symm (C m * X)) g ∈ pZero M i j hij := by
  unfold pGens at hg
  rcases hg with (((hg | hg) | hg) | hg) | hg
  · obtain ⟨p, q, hpq, f, ξ, hf, hA, rfl⟩ := hg
    exact cj_P1_mem hij m hpq hA hf ξ
  · obtain ⟨p, q, hpq, f, ξ, hf, hA, rfl⟩ := hg
    exact cj_P2_mem hij m hpq hA hf ξ
  · obtain ⟨p, q, hpq, f, ξ, hf, hO, rfl⟩ := hg
    rw [z_conj_disj hpq hij.symm hO.2.1.symm hO.2.2.2.symm hO.1.symm hO.2.2.1.symm]
    exact mem_P3 hij hpq hO hf ξ
  · obtain ⟨f, hf, rfl⟩ := hg
    rw [cj_of_commute (x_commute_self hij.symm _ _)]
    exact mem_P4 hij hf rfl
  · obtain ⟨f, hf, rfl⟩ := hg
    rw [cj_x_eq_zElt, show C m * X = X * C m by ring]
    exact zElt_alpha_mem hij hki hkj hf (C m)

#audit_axioms cj_gen_mem

/-- **L–S Lemma 5.9**: `y⁻¹ P̃_α(0) y ⊆ P̃_α(0)` for `y = x_ji(m X)`. -/
theorem cj_mem_pZero {k : I} (hki : k ≠ i) (hkj : k ≠ j) {g : SteinbergGroup I (Polynomial A)}
    (hg : g ∈ pZero M i j hij) : cj (x j i hij.symm (C m * X)) g ∈ pZero M i j hij := by
  unfold pZero at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact cj_gen_mem hij m hki hkj hg
  | one =>
    rw [cj, mul_one, inv_mul_cancel]
    exact one_mem _
  | mul g h _ _ hg hh =>
    rw [cj_mul]
    exact mul_mem hg hh
  | inv g _ hg =>
    rw [show cj (x j i hij.symm (C m * X)) g⁻¹ = (cj (x j i hij.symm (C m * X)) g)⁻¹ by
      unfold cj
      group]
    exact inv_mem hg

#audit_axioms cj_mem_pZero

end Conj

theorem x_neg_inv {i j : I} (hij : i ≠ j) (m : A) :
    (x j i hij.symm (C m * X))⁻¹ = x j i hij.symm (C (-m) * X) := by
  rw [← x_neg, map_neg, neg_mul]

/-- `x_ji(m X)` normalizes `P̃_α(0)`. -/
theorem neg_mem_normalizer {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (m : A) :
    x j i hij.symm (C m * X) ∈ (pZero M i j hij).normalizer := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e := cj_mem_pZero hij (-m) hki hkj hh
    rwa [cj, ← x_neg_inv, inv_inv] at e
  · intro hh
    have e := cj_mem_pZero hij m hki hkj hh
    rwa [cj, show (x j i hij.symm (C m * X))⁻¹ *
      (x j i hij.symm (C m * X) * h * (x j i hij.symm (C m * X))⁻¹) *
      x j i hij.symm (C m * X) = h by group] at e

/-- **L–S Lemma 5.9, normality**: `P̃_α(*)` normalizes `P̃_α(0)`. -/
theorem pStar_le_normalizer {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    pStar M i j hij ≤ (pZero M i j hij).normalizer := by
  rw [pStar, Subgroup.closure_le]
  rintro g (hg | ⟨m, -, rfl⟩)
  · exact Subgroup.le_normalizer (Subgroup.subset_closure hg)
  · exact neg_mem_normalizer hij hki hkj m

theorem conj_mem_pZero {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {g h : SteinbergGroup I (Polynomial A)} (hg : g ∈ pStar M i j hij)
    (hh : h ∈ pZero M i j hij) : g * h * g⁻¹ ∈ pZero M i j hij :=
  (Subgroup.mem_normalizer_iff.mp (pStar_le_normalizer hij hki hkj hg) h).mp hh

#audit_axioms conj_mem_pZero

theorem x_neg_mul {i j : I} (hij : i ≠ j) (m m' : A) :
    x j i hij.symm (C m * X) * x j i hij.symm (C m' * X) = x j i hij.symm (C (m + m') * X) := by
  rw [x_mul, map_add, add_mul]

/-- **L–S Lemma 5.9**: `P̃_α(*) = ⋃_{m ∈ M} P̃_α(0) x_{-α}(m X)`. -/
theorem mem_pStar_iff {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {g : SteinbergGroup I (Polynomial A)} :
    g ∈ pStar M i j hij ↔
      ∃ m ∈ M, ∃ g₀ ∈ pZero M i j hij, g = g₀ * x j i hij.symm (C m * X) := by
  constructor
  · intro hg
    unfold pStar at hg
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      rcases hg with hg | ⟨m, hm, rfl⟩
      · exact ⟨0, zero_mem _, g, Subgroup.subset_closure hg, by rw [map_zero, zero_mul, x_zero,
          mul_one]⟩
      · exact ⟨m, hm, 1, one_mem _, (one_mul _).symm⟩
    | inv_mem g hg =>
      rcases hg with hg | ⟨m, hm, rfl⟩
      · exact ⟨0, zero_mem _, g⁻¹, inv_mem (Subgroup.subset_closure hg), by
          rw [map_zero, zero_mul, x_zero, mul_one]⟩
      · exact ⟨-m, neg_mem hm, 1, one_mem _, by rw [one_mul, x_neg_inv]⟩
    | one => exact ⟨0, zero_mem _, 1, one_mem _, by rw [map_zero, zero_mul, x_zero, mul_one]⟩
    | mul g h hg' hh' hg hh =>
      obtain ⟨m, hm, g₀, hg₀, rfl⟩ := hg
      obtain ⟨m', hm', h₀, hh₀, rfl⟩ := hh
      have hy : x j i hij.symm (C m * X) ∈ pStar M i j hij := neg_mem_pStar M i j hij hm
      refine ⟨m + m', add_mem hm hm', g₀ * (x j i hij.symm (C m * X) * h₀ *
        (x j i hij.symm (C m * X))⁻¹), mul_mem hg₀ (conj_mem_pZero hij hki hkj hy hh₀), ?_⟩
      rw [← x_neg_mul]
      group
  · rintro ⟨m, hm, g₀, hg₀, rfl⟩
    exact mul_mem (pZero_le_pStar M i j hij hg₀) (neg_mem_pStar M i j hij hm)

#audit_axioms mem_pStar_iff

/-- **Uniqueness in Lemma 5.9**: if `g = g₀ x_ji(m X)` with `g₀ ∈ P̃_α(0)`, then `m = p_α(g)`. -/
theorem pAlpha_decomp {i j : I} (hij : i ≠ j) {m : A} (hm : m ∈ M)
    {g₀ : SteinbergGroup I (Polynomial A)} (hg₀ : g₀ ∈ pZero M i j hij) :
    pAlpha i j (g₀ * x j i hij.symm (C m * X)) = m := by
  rw [pAlpha_mul (pZero_le_pStar M i j hij hg₀) (neg_mem_pStar M i j hij hm),
    pAlpha_eq_zero hg₀, pAlpha_x, zero_add]

#audit_axioms pAlpha_decomp

end LSCore
end BooneHigmanLinear
end GroupApproximation
