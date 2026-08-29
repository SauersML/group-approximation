import GroupApproximation.GGT.HullSCUnionGeometryFactorDichotomy

/-!
# Displacement at a syllable boundary

The remaining branch of the acylindricity clause needs to move the two
basepoints from `1` and `t` to the two ends of a long syllable of `t`, and for
that it needs to know that the displacement does not grow in between.  In a
hyperbolic space that is quasi-convexity of the displacement function, with a
constant proportional to `δ`.  At a *syllable boundary* of a free product it
holds with constant zero, and the proof is two lines of the seam calculus.

## The estimate

`wordNorm_le_conj_of_fstIdx_ne`: if `x` and `y` begin in different factors then

    |g| ≤ |x⁻¹ g x|   or   |g| ≤ |y⁻¹ g y| .

`g` begins in at most one of the two factors, so one of the two conjugations has
a free seam on the *conjugator* side --- and that is `wordNorm_branch`, giving
`|z⁻¹ g| = |z| + |g|` exactly.  The triangle inequality
`|z⁻¹ g| ≤ |z⁻¹ g z| + |z|` then cancels the `|z|`.  Nothing is said about the
other seam, and nothing needs to be: the cancellation that can happen there is
already paid for.

## The form the count uses

`wordNorm_conj_le_of_seam`: for a reduced factorisation `t = c * y`,

    |c⁻¹ k c| ≤ |k|   or   |c⁻¹ k c| ≤ |t⁻¹ k t| ,

which is the estimate read at `x := c⁻¹` and `g := c⁻¹ k c`, because then
`x⁻¹ g x = k` and `y⁻¹ g y = t⁻¹ k t`.  So a `k` that displaces `1` and `t` by
at most `ε` displaces *every* syllable boundary of `t` by at most `ε`, and the
two ends of a long syllable become a legitimate pair of basepoints.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section BranchPoint

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-- **A free seam on the conjugator side costs nothing.**  If `z` and `g` begin
in different factors then conjugation by `z` does not shorten `g`. -/
theorem wordNorm_le_conj_of_fstIdx_ne_left
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {z g : CoprodI G}
    (hz : Word.fstIdx (Word.equiv z) ≠ Word.fstIdx (Word.equiv g)) :
    wordNorm (unionCarrier S) g
      ≤ wordNorm (unionCarrier S) (z⁻¹ * g * z) := by
  have hcar := isSymmetricGeneratingSet_unionCarrier hS
  have h1 : wordNorm (unionCarrier S) (z⁻¹ * g)
      = wordNorm (unionCarrier S) z + wordNorm (unionCarrier S) g :=
    wordNorm_branch hS hz
  have h2 := wordNorm_mul_le hcar (z⁻¹ * g * z) z⁻¹
  have h3 : (z⁻¹ * g * z * z⁻¹ : CoprodI G) = z⁻¹ * g := by group
  rw [h3, wordNorm_inv hcar] at h2
  omega

/-- **The branch-point estimate.**  At a point where the two directions leave in
different factors, the displacement is at most the displacement at one of the
two ends. -/
theorem wordNorm_le_conj_of_fstIdx_ne
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {x y g : CoprodI G}
    (h : Word.fstIdx (Word.equiv x) ≠ Word.fstIdx (Word.equiv y)) :
    wordNorm (unionCarrier S) g
        ≤ wordNorm (unionCarrier S) (x⁻¹ * g * x)
      ∨ wordNorm (unionCarrier S) g
        ≤ wordNorm (unionCarrier S) (y⁻¹ * g * y) := by
  by_cases hx : Word.fstIdx (Word.equiv x) = Word.fstIdx (Word.equiv g)
  · refine Or.inr (wordNorm_le_conj_of_fstIdx_ne_left hS ?_)
    intro hcon
    exact h (hx.trans hcon.symm)
  · exact Or.inl (wordNorm_le_conj_of_fstIdx_ne_left hS hx)

/-- **Displacement at a syllable boundary of `t`.**  For a reduced factorisation
`t = c * y`, a `k` displacing `1` and `t` displaces the boundary `c` by no
more. -/
theorem wordNorm_conj_le_of_seam (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {c y : CoprodI G} (hseam : Word.fstIdx (Word.equiv c⁻¹)
      ≠ Word.fstIdx (Word.equiv y)) (k : CoprodI G) :
    wordNorm (unionCarrier S) (c⁻¹ * k * c) ≤ wordNorm (unionCarrier S) k
      ∨ wordNorm (unionCarrier S) (c⁻¹ * k * c)
        ≤ wordNorm (unionCarrier S) ((c * y)⁻¹ * k * (c * y)) := by
  have hkey : wordNorm (unionCarrier S) (c⁻¹ * k * c)
        ≤ wordNorm (unionCarrier S) ((c⁻¹)⁻¹ * (c⁻¹ * k * c) * c⁻¹)
      ∨ wordNorm (unionCarrier S) (c⁻¹ * k * c)
        ≤ wordNorm (unionCarrier S) (y⁻¹ * (c⁻¹ * k * c) * y) :=
    wordNorm_le_conj_of_fstIdx_ne hS hseam
  have h1 : ((c⁻¹)⁻¹ * (c⁻¹ * k * c) * c⁻¹ : CoprodI G) = k := by group
  have h2 : (y⁻¹ * (c⁻¹ * k * c) * y : CoprodI G)
      = (c * y)⁻¹ * k * (c * y) := by group
  rw [h1, h2] at hkey
  exact hkey

/-! ## 2.  A long syllable -/

/-- The identity begins in no factor. -/
theorem fstIdx_one_ne (p : ι) :
    Word.fstIdx (Word.equiv (1 : CoprodI G)) ≠ some p := by
  simp [Word.fstIdx]

private theorem exists_long_syllable_aux
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) :
    ∀ (n : ℕ) (t : CoprodI G), sylLength t ≤ n → t ≠ 1 →
      ∃ (q : ι) (τ : G q) (c r : CoprodI G),
        t = c * CoprodI.of τ * r ∧ τ ≠ 1 ∧
        Word.fstIdx (Word.equiv c⁻¹) ≠ some q ∧
        Word.fstIdx (Word.equiv r) ≠ some q ∧
        (Word.equiv t).toList
          = (Word.equiv c).toList ++ ⟨q, τ⟩ :: (Word.equiv r).toList ∧
        wordNorm (unionCarrier S) t ≤ sylLength t * wordNorm (S q) τ := by
  intro n
  induction n with
  | zero =>
      intro t ht ht1
      exact absurd (sylLength_eq_zero_iff.mp (Nat.le_zero.mp ht)) ht1
  | succ n ih =>
      intro t ht ht1
      obtain ⟨q₁, τ₁, hlead⟩ :
          ∃ (q₁ : ι) (τ₁ : G q₁), lead t = some ⟨q₁, τ₁⟩ := by
        rcases hlt : lead t with _ | ⟨q₁, τ₁⟩
        · exact absurd (lead_eq_none_iff.mp hlt) ht1
        · exact ⟨q₁, τ₁, rfl⟩
      obtain ⟨t', hteq, hτ₁1, ht'idx, htlist⟩ := exists_split_toList hlead
      have hlen : sylLength t = sylLength t' + 1 := by
        simp only [sylLength, htlist, List.length_cons]
      have hnorm : wordNorm (unionCarrier S) t
          = wordNorm (S q₁) τ₁ + wordNorm (unionCarrier S) t' := by
        rw [hteq]
        exact wordNorm_of_mul hS hτ₁1 ht'idx
      by_cases ht'1 : t' = 1
      · refine ⟨q₁, τ₁, 1, 1, ?_, hτ₁1, ?_, ?_, ?_, ?_⟩
        · rw [hteq, ht'1]
          group
        · rw [inv_one]
          exact fstIdx_one_ne q₁
        · exact fstIdx_one_ne q₁
        · rw [htlist, ht'1, toList_equiv_one, List.nil_append]
        · have hz0 : wordNorm (unionCarrier S) (1 : CoprodI G) = 0 :=
            wordNorm_one _
          have hz1 : sylLength (1 : CoprodI G) = 0 :=
            sylLength_eq_zero_iff.mpr rfl
          rw [ht'1] at hnorm hlen
          have h0 : wordNorm (unionCarrier S) t = wordNorm (S q₁) τ₁ := by omega
          have h1 : sylLength t = 1 := by omega
          rw [h0, h1]
          omega
      · obtain ⟨q, τ, c', r, ht'eq, hτ1, hc'idx, hridx, ht'list, hbound⟩ :=
          ih t' (by omega) ht'1
        have hc'app : (Word.equiv t').toList
            = (Word.equiv c').toList
              ++ (Word.equiv (CoprodI.of τ * r)).toList := by
          rw [ht'list, toList_equiv_of_mul hτ1 hridx]
        have hc'fst : Word.fstIdx (Word.equiv c') ≠ some q₁ :=
          fstIdx_of_append_ne hc'app ht'idx
        by_cases hcmp : wordNorm (S q₁) τ₁ ≤ wordNorm (S q) τ
        · refine ⟨q, τ, CoprodI.of τ₁ * c', r, ?_, hτ1, ?_, hridx, ?_, ?_⟩
          · rw [hteq, ht'eq]
            group
          · have hτinv : ((CoprodI.of τ₁ : CoprodI G)⁻¹) = CoprodI.of τ₁⁻¹ :=
              (map_inv (CoprodI.of : G q₁ →* CoprodI G) τ₁).symm
            have hinv : ((CoprodI.of τ₁ * c')⁻¹ : CoprodI G)
                = c'⁻¹ * CoprodI.of τ₁⁻¹ := by
              rw [mul_inv_rev, hτinv]
            rw [hinv]
            by_cases hc'1 : c' = 1
            · have hl : (Word.equiv t').toList
                  = ⟨q, τ⟩ :: (Word.equiv r).toList := by
                rw [ht'list, hc'1, toList_equiv_one, List.nil_append]
              have hq : Word.fstIdx (Word.equiv t') = some q := by
                simp [Word.fstIdx, hl]
              have hqne : q ≠ q₁ := by
                intro hcon
                rw [hcon] at hq
                exact ht'idx hq
              rw [hc'1, inv_one, one_mul, fstIdx_of_single (inv_ne_one.mpr hτ₁1)]
              intro hcon
              exact hqne (Option.some.inj hcon).symm
            · have hseam : Word.fstIdx (Word.equiv (c'⁻¹)⁻¹)
                  ≠ Word.fstIdx (Word.equiv (CoprodI.of τ₁⁻¹ : CoprodI G)) := by
                rw [inv_inv, fstIdx_of_single (inv_ne_one.mpr hτ₁1)]
                exact hc'fst
              rw [fstIdx_mul_of_seam (inv_ne_one.mpr hc'1) hseam]
              exact hc'idx
          · rw [htlist, ht'list, toList_equiv_of_mul hτ₁1 hc'fst, List.cons_append]
          · rw [hnorm, hlen, add_mul, one_mul]
            omega
        · refine ⟨q₁, τ₁, 1, t', ?_, hτ₁1, ?_, ht'idx, ?_, ?_⟩
          · rw [hteq, one_mul]
          · rw [inv_one]
            exact fstIdx_one_ne q₁
          · rw [htlist, toList_equiv_one, List.nil_append]
          · have hle : wordNorm (S q) τ ≤ wordNorm (S q₁) τ₁ := by omega
            have hmul : sylLength t' * wordNorm (S q) τ
                ≤ sylLength t' * wordNorm (S q₁) τ₁ :=
              Nat.mul_le_mul (le_refl (sylLength t')) hle
            rw [hnorm, hlen, add_mul, one_mul]
            omega

/-- **Some syllable of `t` carries its share of the length.**  A word of `n`
syllables has one whose factor length is at least `|t| / n`, split off with both
seams free. -/
theorem exists_long_syllable (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {t : CoprodI G} (ht : t ≠ 1) :
    ∃ (q : ι) (τ : G q) (c r : CoprodI G),
      t = c * CoprodI.of τ * r ∧ τ ≠ 1 ∧
      Word.fstIdx (Word.equiv c⁻¹) ≠ some q ∧
      Word.fstIdx (Word.equiv r) ≠ some q ∧
      (Word.equiv t).toList
        = (Word.equiv c).toList ++ ⟨q, τ⟩ :: (Word.equiv r).toList ∧
      wordNorm (unionCarrier S) t ≤ sylLength t * wordNorm (S q) τ :=
  exists_long_syllable_aux hS (sylLength t) t le_rfl ht

end BranchPoint

end HullSCUnionGeometry
end GroupApproximation
