import GroupApproximation.BooneHigmanLinear.LSCore.PStar
import GroupApproximation.BooneHigmanLinear.RelGen.Statements
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.Polynomial.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `K(A[X], M[X]) ≤ P̃_α(*)` (Lavrenov–Sinchuk, Lemma 5.12), and `p_α` on `z_{-α}` (Remark 5.14)

For `α = (i, j)`:
* `x_mem_pStar`: every `x_β(s)` with `s ∈ X·M[X]` lies in `P̃_α(*)`. For `β = -α` write
  `s = m X + X² f₁` with `m ∈ M`.
* `relKer_xPoly_le_pStar`: `St̄(A[X], X·M[X]) ≤ P̃_α(*)`, from Stepanov's Theorem 4.4
  (`RelGen.Thm44Statement`, lane bh-pal-wire). It is applied to the parabolic set
  `S = {(p, q) | p ∈ {i, j} ∨ q ∉ {i, j}}`, whose special part consists of `Adj` roots.
* `polyKer_le_pStar` (**Lemma 5.12**): for a local ring `A` with maximal ideal `M`,
  `K(A[X], M[X]) ≤ P̃_α(*)`, from Corollary 4.10 (`RelGen.Cor410Statement`) with the acute root
  `(i, k)`.
* `pAlpha_zElt_neg` (**Remark 5.14**): `p_α(z_{-α}(s, ξ)) = s₁`, the `X`-coefficient of `s`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen
open Polynomial (X C)

variable {I : Type} [Fintype I] [DecidableEq I] {A : Type} [CommRing A] {M : Ideal A}

theorem exists_X_mul {s : Polynomial A} (hs : s ∈ xPolyIdeal M) :
    ∃ f ∈ polyIdeal M, s = X * f := by
  obtain ⟨f, hf, rfl⟩ := Ideal.mem_span_singleton_mul.mp hs
  exact ⟨f, hf, rfl⟩

/-- `X f = m X + X² f₁` with `m = f(0) ∈ M` and `f₁ ∈ M[X]`. -/
theorem X_mul_split {f : Polynomial A} (hf : f ∈ polyIdeal M) :
    f.coeff 0 ∈ M ∧ f.divX ∈ polyIdeal M ∧ X * f = C (f.coeff 0) * X + X ^ 2 * f.divX := by
  have hc := Ideal.mem_map_C_iff.mp hf
  refine ⟨hc 0, Ideal.mem_map_C_iff.mpr fun n => ?_, ?_⟩
  · rw [Polynomial.coeff_divX]
    exact hc (n + 1)
  · conv_lhs => rw [← Polynomial.X_mul_divX_add f]
    ring

/-- `x_β(s) ∈ P̃_α(*)` for every root `β` and `s ∈ X·M[X]`. -/
theorem x_mem_pStar {i j : I} (hij : i ≠ j) {p q : I} (hpq : p ≠ q) {s : Polynomial A}
    (hs : s ∈ xPolyIdeal M) : x p q hpq s ∈ pStar M i j hij := by
  obtain ⟨f, hf, rfl⟩ := exists_X_mul hs
  have hXf : X * f ∈ polyIdeal M := Ideal.mul_mem_left _ _ hf
  by_cases hA : Adj i j p q
  · exact pZero_le_pStar M i j hij (x_mem_P1 hij hpq hA hf rfl)
  · by_cases hO : Orth i j p q
    · exact pZero_le_pStar M i j hij (x_mem_P3 hij hpq hO hXf)
    · -- `β = ±α`
      have hpm : (p = i ∧ q = j) ∨ (p = j ∧ q = i) := by
        unfold Adj at hA
        unfold Orth at hO
        by_contra hc
        apply hA
        refine ⟨?_, fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
        by_contra hn
        simp only [not_or] at hn
        exact hO ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩
      rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact pZero_le_pStar M _ _ hij (mem_P5 hij hXf)
      · obtain ⟨hm, hf₁, he⟩ := X_mul_split hf
        rw [he, ← x_mul]
        exact mul_mem (neg_mem_pStar M _ _ hij hm)
          (pZero_le_pStar M _ _ hij (mem_P4 hij hf₁ rfl))

#audit_axioms x_mem_pStar

/-- The parabolic set `S = {(p, q) | p ∈ {i, j} ∨ q ∉ {i, j}}`. -/
def parS (i j : I) : I → I → Prop :=
  fun p q => p = i ∨ p = j ∨ (q ≠ i ∧ q ≠ j)

theorem parS_parabolic (i j : I) : IsParabolicRoots (parS i j) := by
  refine ⟨fun a b c _ hab hbc => ?_, fun p q _ => ?_⟩
  · rcases hab with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hbc with h' | h' | h'
      · exact absurd h' h.1
      · exact absurd h' h.2
      · exact Or.inr (Or.inr h')
  · by_cases hp : p = i ∨ p = j
    · exact Or.inl (by rcases hp with h | h <;> simp [parS, h])
    · by_cases hq : q ≠ i ∧ q ≠ j
      · exact Or.inl (Or.inr (Or.inr hq))
      · right
        simp only [not_and_or, not_not] at hq
        rcases hq with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)

theorem adj_of_specialPart {i j p q : I} (h : specialPart (parS i j) p q) : Adj i j p q := by
  obtain ⟨-, hn⟩ := h
  unfold parS at hn
  simp only [not_or, not_and_or, not_not] at hn
  obtain ⟨hqi, hqj, hp⟩ := hn
  refine ⟨?_, fun h => hqj h.2, fun h => hqi h.2⟩
  rcases hp with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- `St̄(A[X], X·M[X]) ≤ P̃_α(*)`, from Stepanov's Theorem 4.4. -/
theorem relKer_xPoly_le_pStar (h44 : Thm44Statement) (h3 : ThirdIndex I) {i j : I}
    (hij : i ≠ j) : relKer I (xPolyIdeal M) ≤ pStar M i j hij := by
  obtain ⟨k, hik, hjk⟩ := h3 i j
  have hne : ∃ a b : I, a ≠ b ∧ specialPart (parS i j) a b :=
    ⟨i, k, hik, Or.inl rfl, by
      unfold parS
      simp only [not_or, not_and_or, not_not]
      exact ⟨hik.symm, fun h => hjk h.symm, Or.inl rfl⟩⟩
  rw [h44 I h3 (parS i j) (parS_parabolic i j) hne (Polynomial A) (xPolyIdeal M), zGen,
    Subgroup.closure_le]
  rintro g (⟨p, q, hpq, s, hs, rfl⟩ | ⟨p, q, hpq, s, ξ, hU, hs, rfl⟩)
  · exact x_mem_pStar hij hpq hs
  · obtain ⟨f, hf, rfl⟩ := exists_X_mul hs
    exact pZero_le_pStar M i j hij (mem_P1 hij hpq (adj_of_specialPart hU) hf rfl ξ)

#audit_axioms relKer_xPoly_le_pStar

/-- **L–S Lemma 5.12**: `K(A[X], M[X]) ≤ P̃_α(*)` for a local ring `A`, `M = 𝔪`. -/
theorem polyKer_le_pStar [IsLocalRing A] (h44 : Thm44Statement) (h410 : Cor410Statement)
    (h3 : ThirdIndex I) {i j : I} (hij : i ≠ j) :
    polyKer I (IsLocalRing.maximalIdeal A) ≤ pStar (IsLocalRing.maximalIdeal A) i j hij := by
  obtain ⟨k, hik, hjk⟩ := h3 i j
  rw [h410 I h3 A i k hik, sup_le_iff, Subgroup.closure_le]
  refine ⟨relKer_xPoly_le_pStar h44 h3 hij, ?_⟩
  rintro _ ⟨m, η, hm, rfl⟩
  exact pZero_le_pStar _ i j hij (cElt_mem_acute hij hik (Or.inl ⟨rfl, fun h => hjk h.symm⟩)
    (Ideal.mem_map_of_mem _ hm) η)

#audit_axioms polyKer_le_pStar

/-- **L–S Remark 5.14**: `p_α(z_{-α}(s, ξ))` is the `X`-coefficient of `s`. -/
theorem pAlpha_zElt_neg {i j : I} (hij : i ≠ j) (s ξ : Polynomial A) :
    pAlpha i j (zElt j i hij.symm s ξ) = s.coeff 1 := by
  have hR : ∀ k, (1 + Matrix.single i j ξ) k i = (1 : Matrix I I (Polynomial A)) k i :=
    fun k => by
      rw [Matrix.add_apply, Matrix.single_apply_of_ne (fun h => hij h.2.symm), add_zero]
  have hP : ∀ k, (1 + Matrix.single i j (-ξ)) j k = (1 : Matrix I I (Polynomial A)) j k :=
    fun k => by rw [Matrix.add_apply, Matrix.single_apply_of_ne (fun h => hij h.1), add_zero]
  have e : (mat (zElt j i hij.symm s ξ)) j i = s := by
    rw [zElt, mat_mul, mat_mul, mat_x, mat_x, mat_x, Matrix.mul_apply]
    simp_rw [hR]
    rw [← Matrix.mul_apply, mul_one, Matrix.mul_apply]
    simp_rw [hP]
    rw [← Matrix.mul_apply, one_mul, Matrix.add_apply, Matrix.one_apply_ne hij.symm,
      Matrix.single_apply_same, zero_add]
  rw [pAlpha, e]

#audit_axioms pAlpha_zElt_neg

end LSCore
end BooneHigmanLinear
end GroupApproximation
