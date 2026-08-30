import GroupApproximation.GGT.DGOLemma421Statement

/-!
# The direct consumer of DGO Lemma 4.21(a)

The statement layer for Lemma 4.21 must not remain an unused named `Prop`.
This module records its first actual consequence: if `a` is a base letter
outside `H_λ` and `h ∈ H_λ` is beyond the uniform relative-ball
threshold, then `a h` is loxodromic on the relative Cayley graph.

The proof is the literal consumer of clause (a).  The word `(a h)^n` has length
`2n`, satisfies (W1)--(W3), and clause (a) gives

`2n ≤ 4 |(a h)^n| + 4`.

Thus the orbit has lower slope `1/2` and additive error `1`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Lemma 4.21(a) gives the deep-letter loxodromy threshold.**

The threshold is uniform in `λ`, `a` and `h`, because the constant in
`DGOLemma421a` is chosen immediately after the relative generating set. -/
theorem exists_threshold_isLoxodromic_mul_of_dgoLemma421a
    (h421a : DGOLemma421a.{u, w}) (D : RelGenSet G Λ)
    (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ C : ℕ, ∀ (lam : Λ) (a : G), a ∈ D.base → a ∉ D.fam lam →
      ∀ h ∈ D.fam lam, h ∉ D.relBall lam C →
        IsLoxodromic (a * h) (Cayley.base D.alphabet) := by
  obtain ⟨C, hquasi⟩ := h421a G Λ D hemb.hyperbolic
  refine ⟨C, ?_⟩
  intro lam a ha haH h hh hdeep
  refine ⟨(1 / 2 : ℝ), by norm_num, 1, by norm_num, ?_⟩
  intro n
  let u : List (RelLetter G Λ) :=
    blockWord lam [RelLetter.base a] h n
  have hlet : ∀ c ∈ u, D.IsLetter c := by
    apply isLetter_of_mem_blockWord D lam (h := h) (n := n)
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst c
      exact ha
    · exact hh
  have hW1 : WWord.IsWOne u := by
    exact isWOne_blockWord_singleBase lam a h n
  have hW2 : WWord.IsWTwo D C u := by
    exact isWTwo_blockWord_singleBase D lam hdeep n
  have hW3 : WWord.IsWThree D u := by
    exact isWThree_blockWord_singleBase D lam haH n
  have hbound := hquasi (1 : G) u hlet hW1 hW2 hW3
    0 u.length (Nat.zero_le _) (le_refl _)
  have hlen : u.length = 2 * n := by
    dsimp [u]
    rw [length_blockWord, List.length_singleton]
    omega
  have hend : vertex (1 : G) u u.length = (a * h) ^ n := by
    rw [vertex_length, one_mul]
    dsimp [u]
    simpa [RelLetter.listVal, RelLetter.val] using
      (listVal_blockWord lam [RelLetter.base a] h n)
  rw [Nat.sub_zero, vertex_zero, hend, hlen] at hbound
  have hboundReal :
      ((2 * n : ℕ) : ℝ) ≤
        4 * (wordDist D.alphabet.carrier 1 ((a * h) ^ n) : ℝ) + 4 := by
    exact_mod_cast hbound
  rw [Cayley.dist_eq, Cayley.val_base, Cayley.val_smul, Cayley.val_base,
    mul_one]
  push_cast at hboundReal ⊢
  linarith

end OsinComponents
end GGT
end GroupApproximation
