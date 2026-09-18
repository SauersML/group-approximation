import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet

/-!
# GL06h2: linear progress excludes short conjugates

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121).

If `|x^m| ≥ m T` for every `m`, then no conjugate `g x g⁻¹` has word norm below `T`: from
`x^m = g⁻¹ (g x g⁻¹)^m g` the norm `|x^m|` grows with slope at most `|g x g⁻¹|`.

* `false_of_linear_progress_of_conj`: the contradiction.
* `wordNorm_listVal_le_of_symmetricLabel`: a word over the symmetric label alphabet spells an
  element of word norm at most its length.
-/

namespace GroupApproximation.Full.GL06h2

universe u w

open GroupApproximation.WordMetric
open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

variable {G : Type u} [Group G]

theorem conj_pow_mul_inv (g x : G) (m : ℕ) : (g * x * g⁻¹) ^ m = g * x ^ m * g⁻¹ := by
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, mul_inv_cancel]
  | succ k ih =>
      rw [pow_succ (g * x * g⁻¹) k, ih, pow_succ x k]
      simp only [mul_assoc, inv_mul_cancel_left]

theorem wordNorm_pow_le {S : Set G} (hS : IsSymmetricGeneratingSet S) (h : G) (m : ℕ) :
    wordNorm S (h ^ m) ≤ m * wordNorm S h := by
  induction m with
  | zero =>
      rw [pow_zero, wordNorm_one]
      exact Nat.zero_le _
  | succ k ih =>
      rw [pow_succ]
      calc wordNorm S (h ^ k * h) ≤ wordNorm S (h ^ k) + wordNorm S h :=
            wordNorm_mul_le hS _ _
        _ ≤ k * wordNorm S h + wordNorm S h := Nat.add_le_add_right ih _
        _ = (k + 1) * wordNorm S h := by ring

theorem wordNorm_conj_le {S : Set G} (hS : IsSymmetricGeneratingSet S) (g y : G) :
    wordNorm S (g * y * g⁻¹) ≤ 2 * wordNorm S g + wordNorm S y := by
  have h1 := wordNorm_mul_le hS (g * y) g⁻¹
  have h2 := wordNorm_mul_le hS g y
  rw [wordNorm_inv hS] at h1
  omega

/-- **Linear progress excludes short conjugates** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem false_of_linear_progress_of_conj {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {x h g : G} {T : ℕ} (hprog : ∀ m : ℕ, m * T ≤ wordNorm S (x ^ m))
    (hshort : wordNorm S h < T) (hconj : h = g * x * g⁻¹) : False := by
  have hx1 : x = g⁻¹ * h * g⁻¹⁻¹ := by
    rw [hconj]
    group
  have hx : ∀ m : ℕ, x ^ m = g⁻¹ * h ^ m * g⁻¹⁻¹ := by
    intro m
    rw [← conj_pow_mul_inv, ← hx1]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 * wordNorm S g⁻¹ + 1 := ⟨_, rfl⟩
  have h1 := hprog m
  have h2 := wordNorm_conj_le hS g⁻¹ (h ^ m)
  rw [← hx m] at h2
  have h3 := wordNorm_pow_le hS h m
  have hs : wordNorm S h + 1 ≤ T := hshort
  have h4 := Nat.mul_le_mul_left m hs
  rw [Nat.mul_add, Nat.mul_one] at h4
  omega

/-- A word over `symmetricLabelAlphabet D` spells an element of word norm at most its length, in
the original alphabet of `D`. -/
theorem wordNorm_listVal_le_of_symmetricLabel {Lambda : Type w} (D : RelGenSet G Lambda)
    (u : List (RelLetter G Lambda)) (hu : ∀ x ∈ u, (symmetricLabelAlphabet D).IsLetter x) :
    wordNorm D.alphabet.carrier (RelLetter.listVal u) ≤ u.length := by
  have h := OsinComponents.wordNorm_listVal_le (symmetricLabelAlphabet D) u hu
  rw [symmetricLabelAlphabet.wordNorm_eq] at h
  exact h

end GroupApproximation.Full.GL06h2
