import GroupApproximation.BooneHigmanLinear.LSCore.PAlpha
import GroupApproximation.Meta.AxiomGuard

/-!
# `P̃_α(0)` is normalized by `x_{-α}(m X)` (Lavrenov–Sinchuk, Lemma 5.9, computations (5.5)–(5.8))

For `α = (i, j)` and `m ∈ M`, conjugation by `y = x_ji(m X)` (`g ↦ y⁻¹ g y`) maps each
generator of `P̃_α(0)` into `P̃_α(0)` (`cj_gen_mem`), hence all of `P̃_α(0)` (`cj_mem_pZero`):
* P1 and P2: Lemma 4.1(2), (3) (`z_conj_obtuse_row/col`, `z_conj_acute_row/col` for the root
  `(j, i)`) produce a P4 factor and a P1 factor, (5.5)–(5.7);
* P3 and P4 commute with `y`;
* P5: `x_ij(f)^y = z_ij(f, m X)`, and `z_ij(f, X ξ) ∈ P̃_α(0)` for every `ξ ∈ A[X]`
  (`zElt_alpha_mem`) by Lemma 4.1(5) through a third index `k`, (5.8).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (zElt polyIdeal)
open Polynomial (X C)

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [CommRing A] {M : Ideal A}

theorem adj_row_left {i j l : I} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) : Adj i j i l :=
  ⟨Or.inl rfl, fun h => hlj h.2, fun h => hij h.1⟩

theorem adj_row_right {i j l : I} (hij : i ≠ j) (hli : l ≠ i) : Adj i j j l :=
  ⟨Or.inr (Or.inl rfl), fun h => hij h.1.symm, fun h => hli h.2⟩

theorem adj_col_left {i j k : I} (hkj : k ≠ j) (hki : k ≠ i) : Adj i j k i :=
  ⟨Or.inr (Or.inr (Or.inl rfl)), fun h => hki h.1, fun h => hkj h.1⟩

theorem adj_col_right {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) : Adj i j k j :=
  ⟨Or.inr (Or.inr (Or.inr rfl)), fun h => hki h.1, fun h => hij h.2.symm⟩

/-- **L–S (5.8)**: `z_α(f, X ξ) ∈ P̃_α(0)` for every `ξ ∈ A[X]`, via a third index `k`. -/
theorem zElt_alpha_mem {i j k : I} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {f : Polynomial A}
    (hf : f ∈ polyIdeal M) (ξ : Polynomial A) : zElt i j hij f (X * ξ) ∈ pZero M i j hij := by
  have hjk : j ≠ k := hkj.symm
  have hik : i ≠ k := hki.symm
  have hnf : -f ∈ polyIdeal M := neg_mem hf
  have hff : -f * -ξ ∈ polyIdeal M := Ideal.mul_mem_right _ _ hnf
  have hf2 : f * ξ ^ 2 ∈ polyIdeal M := Ideal.mul_mem_right _ _ hf
  have h := z_add_eq hij hjk hik (-f) (-ξ) X
  rw [show -(-f) = f by ring, show -(-ξ * X) = X * ξ by ring] at h
  have hL : zElt i k hik (-f * X) (-ξ) ∈ pZero M i j hij :=
    mem_P1 hij hik (adj_row_left hij hki hkj) hnf (by ring) (-ξ)
  have hF : x i j hij (-f) * x k j hjk.symm (-(-f * -ξ)) * x j k hjk (-f * -ξ * X ^ 2) *
      x i k hik (-f * X) ∈ pZero M i j hij :=
    mul_mem (mul_mem (mul_mem (mem_P5 hij hnf)
      (x_mem_P2 hij hjk.symm (Or.inr ⟨rfl, hki⟩) (neg_mem hff)))
      (x_mem_P1 hij hjk (adj_row_right hij hki) (Ideal.mul_mem_right X _ hff) (by ring)))
      (x_mem_P1 hij hik (adj_row_left hij hki hkj) hnf (by ring))
  have hG1 : x j i hij.symm (-(-f * (-ξ) ^ 2 * X ^ 2)) ∈ pZero M i j hij :=
    mem_P4 hij hf2 (by ring)
  have hG2 : x k i hik.symm (-(-f * (-ξ) ^ 2 * X)) ∈ pZero M i j hij :=
    x_mem_P1 hij hik.symm (adj_col_left hkj hki) hf2 (by ring)
  have hG3 : zElt k j hjk.symm (-f * -ξ) (-X) ∈ pZero M i j hij :=
    mem_P2 hij hjk.symm (Or.inr ⟨rfl, hki⟩) hff (-1) (by ring)
  rw [h] at hL
  exact (mul_mem_cancel_left hF).mp ((mul_mem_cancel_right hG1).mp
    ((mul_mem_cancel_right hG2).mp ((mul_mem_cancel_right hG3).mp hL)))

#audit_axioms zElt_alpha_mem

/-- `x_ij(f)^{x_ji(ξ)} = z_ij(f, ξ)`. -/
theorem cj_x_eq_zElt {i j : I} (hij : i ≠ j) (f ξ : Polynomial A) :
    cj (x j i hij.symm ξ) (x i j hij f) = zElt i j hij f ξ := by
  rw [cj, zElt, x_neg]

theorem x_commute_self {i j : I} (hij : i ≠ j) (a b : Polynomial A) :
    Commute (x i j hij a) (x i j hij b) := by
  rw [commute_iff_eq, x_mul, x_mul, add_comm]

section Conj

variable {i j : I} (hij : i ≠ j) (m : A)

/-- **L–S (5.5)–(5.7)**: conjugating a P1 generator by `x_ji(m X)`. -/
theorem cj_P1_mem {p q : I} (hpq : p ≠ q) (hA : Adj i j p q) {f : Polynomial A}
    (hf : f ∈ polyIdeal M) (ξ : Polynomial A) :
    cj (x j i hij.symm (C m * X)) (zElt p q hpq (X * f) ξ) ∈ pZero M i j hij := by
  have hc : f * C m ∈ polyIdeal M := Ideal.mul_mem_right _ _ hf
  obtain ⟨hr, hn1, hn2⟩ := hA
  rcases hr with rfl | rfl | rfl | rfl
  · -- β = (i, q), obtuse for (j, i)
    have hqj : q ≠ j := fun h => hn1 ⟨rfl, h⟩
    rw [z_conj_obtuse_row hij.symm hpq (fun h => hqj h.symm)]
    exact mul_mem (mul_mem (mem_P4 hij (neg_mem (Ideal.mul_mem_right ξ _ hc)) (by ring))
      (x_mem_P1 hij _ (adj_row_right hij (fun h => hpq h.symm)) (Ideal.mul_mem_right X _
        (neg_mem hc)) (by ring))) (mem_P1 hij hpq ⟨Or.inl rfl, hn1, hn2⟩ hf rfl ξ)
  · -- β = (j, q), acute for (j, i)
    have hqi : q ≠ i := fun h => hn2 ⟨rfl, h⟩
    rw [z_conj_acute_row hij.symm hpq hqi]
    exact mul_mem (mul_mem (mem_P4 hij (Ideal.mul_mem_right ξ _ hc) (by ring))
      (x_mem_P1 hij _ (adj_col_left (fun h => hpq h.symm) hqi)
        (Ideal.mul_mem_right X _ (neg_mem (Ideal.mul_mem_right (ξ ^ 2) _ hc))) (by ring)))
      (mem_P1 hij hpq ⟨Or.inr (Or.inl rfl), hn1, hn2⟩ hf rfl ξ)
  · -- β = (p, i), acute for (j, i)
    have hpj : p ≠ j := fun h => hn2 ⟨h, rfl⟩
    rw [z_conj_acute_col hij.symm (fun h => hpj h.symm) hpq]
    exact mul_mem (mul_mem (mem_P4 hij (Ideal.mul_mem_right ξ _ hc) (by ring))
      (x_mem_P1 hij _ (adj_row_right hij hpq)
        (Ideal.mul_mem_right X _ (Ideal.mul_mem_right (ξ ^ 2) _ hc)) (by ring)))
      (mem_P1 hij hpq ⟨Or.inr (Or.inr (Or.inl rfl)), hn1, hn2⟩ hf rfl ξ)
  · -- β = (p, j), obtuse for (j, i)
    have hpi : p ≠ i := fun h => hn1 ⟨h, rfl⟩
    rw [z_conj_obtuse_col hij.symm hpq hpi]
    exact mul_mem (mul_mem (mem_P4 hij (neg_mem (Ideal.mul_mem_right ξ _ hc)) (by ring))
      (x_mem_P1 hij _ (adj_col_left hpq hpi) (Ideal.mul_mem_right X _ hc) (by ring)))
      (mem_P1 hij hpq ⟨Or.inr (Or.inr (Or.inr rfl)), hn1, hn2⟩ hf rfl ξ)

#audit_axioms cj_P1_mem

end Conj

end LSCore
end BooneHigmanLinear
end GroupApproximation
