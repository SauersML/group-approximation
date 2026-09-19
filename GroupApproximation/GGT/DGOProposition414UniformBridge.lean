import GroupApproximation.GGT.DGOProposition414Uniform
import GroupApproximation.GGT.DGOLemma421Proof

/-!
# Linear sum bounds in the DGO radius form

The balanced-surgery reduction concludes with `SumBound`, whose quasi-geodesic
inequality has parameters `(1,b)` written as subtraction by `b`.  This file
converts a linear family of those bounds into the radius-witness formulation
used by `DGOUniformSumBound`, with the zero-side polygon handled directly.
The conversion is the fixed-parameter interface needed by the DGO Lemma
4.21 argument.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- A zero-side polygon has an empty word, so its distinguished sum is zero. -/
theorem sumBound_zero
    (D : RelGenSet G Λ) (b : ℝ) (K : ℕ) :
    SumBound D b 0 K := by
  intro v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro s hs
    have hs0 := hI s hs
    omega
  · simp

/-- A linear family of `SumBound`s yields one positive DGO radius constant.
The successor of the linear coefficient is used so positivity is explicit. -/
theorem exists_dgoUniformSumBound_of_linearSumBound
    (D : RelGenSet G Λ) (b : ℕ)
    (hlin : ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n →
      SumBound D (b : ℝ) n (L * n)) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D 1 (b : ℝ) C := by
  obtain ⟨L, hL⟩ := hlin
  refine ⟨L + 1, Nat.zero_lt_succ L, ?_⟩
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  by_cases hn : n = 0
  · subst n
    obtain ⟨r, hr, hsum⟩ := sumBound_zero D (b : ℝ) (L + 1) v word cut I lam
      hlet hclosed hcut hI hedge hcomp hiso (by
        intro s hs
        omega)
    refine ⟨r, hr, ?_⟩
    have hIempty : I = ∅ := by
      ext s
      constructor
      · intro hs
        have hs0 := hI s hs
        omega
      · intro hs
        simp at hs
    simp [hIempty]
  · have hnpos : 1 ≤ n := by omega
    have hsum := hL n hnpos
    obtain ⟨r, hr, htotal⟩ := hsum v word cut I lam hlet hclosed hcut hI
      hedge hcomp hiso (by
        intro s hs hnot p q hp hpq hq
        have hq' := hquasi s hs hnot p q hp hpq hq
        norm_num at hq' ⊢
        exact hq')
    refine ⟨r, hr, ?_⟩
    have hlinTotal : (∑ s ∈ I, r s) ≤ L * n := htotal
    have hsucc : L * n ≤ (L + 1) * n := by
      exact Nat.mul_le_mul_right n (by omega)
    exact le_trans hlinTotal hsucc

end OsinComponents
end GGT
end GroupApproximation
