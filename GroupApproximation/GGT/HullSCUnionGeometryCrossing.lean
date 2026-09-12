import GroupApproximation.GGT.HullSCUnionGeometryConcat

/-!
# The crossing estimate: the no-seam case, and the peel

`GGT/HullSCUnionGeometryAcylindrical.lean` reduces acylindricity of the union
alphabet to bounding `conjDisplacement A ε t = {k : |k| ≤ ε ∧ |t⁻¹kt| ≤ ε}` for
`|t|` large.  This module settles the case where nothing cancels, and supplies
the induction step for the rest.

* `wordNorm_conj_of_no_seam` --- if `k ≠ 1` and *neither* end of `k` lies in the
  factor `t` begins in, then `|t⁻¹kt| = 2|t| + |k|` exactly.  So
  `two_mul_wordNorm_le_conj` puts `|t| ≤ ε/2`, and that configuration is excluded
  as soon as `R > ε`.
* `conj_seam_cases` is the resulting trichotomy, which is the case split the
  whole estimate runs on.
* `conj_peel` is the induction step for the two remaining branches: peeling the
  leading syllable `u` of `t` replaces the pair `(t, k)` by
  `(t', u⁻¹ k u)` with one syllable fewer, and leaves `t⁻¹kt` unchanged.

The head computation `fstIdx_equiv_inv_mul` is what makes the no-seam case
usable: the concatenation form of the branch lemma says the reduced word of
`p⁻¹m` starts with the inverse of the *last* syllable of `p`, so the back seam of
`t⁻¹k` against `t` is readable from the front of `k⁻¹`.

## What is left

Two branches of `conj_seam_cases`, and after `conj_peel` they are the same two
at one syllable fewer.  The induction stops in one of two configurations:

* `k` is conjugate into a single factor by a prefix of `t` --- and then, once the
  remaining syllable of `t` is long, the count is the *factor's* own
  acylindricity, in the conjugation form
  `isAcylindrical_cayley_of_conjDisplacement` puts it in;
* the lineal configuration, where `t` and `k` share a cyclic reduction: by
  `FreeProductCyclic.exists_cyclicReduction` write `t = c · s · c⁻¹` with `s`
  cyclically reduced, and `k ∈ c · ⟨s⟩ · c⁻¹` up to bounded error, so `k` is
  determined by an integer that `|k| ≤ ε` bounds.

The second is the branch the naive tree argument gets wrong (see the refutation
in `GGT/HullSCUnionGeometryAcylindrical.lean`), and it is the one still owed.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section Crossing

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-! ## 1.  The head of a product in which nothing cancels -/

/-- **A no-cancellation product begins where the inverse of its left factor
begins.**  By the concatenation form of the branch lemma the reduced word of
`p⁻¹m` is `invList p‾ ++ m‾`, and the first block is nonempty when `p ≠ 1`. -/
theorem fstIdx_equiv_inv_mul {p m : CoprodI G} (hp : p ≠ 1)
    (h : Word.fstIdx (Word.equiv p) ≠ Word.fstIdx (Word.equiv m)) :
    Word.fstIdx (Word.equiv (p⁻¹ * m)) = Word.fstIdx (Word.equiv p⁻¹) := by
  have hlist := toList_equiv_inv_mul_of_fstIdx_ne h
  have hinv : (Word.equiv p⁻¹).toList
      = CoprodIWordInverse.invList (Word.equiv p).toList := by
    rw [CoprodIWordInverse.equiv_inv]; rfl
  have hne : CoprodIWordInverse.invList (Word.equiv p).toList ≠ [] := by
    intro hnil
    have hlen : (Word.equiv p).toList.length = 0 := by
      have h0 := congrArg List.length hnil
      rwa [CoprodIWordInverse.length_invList] at h0
    exact hp (sylLength_eq_zero_iff.mp (by simpa [sylLength] using hlen))
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
  simp only [Word.fstIdx, hlist, hinv, hal, List.cons_append, List.head?_cons]

/-! ## 2.  The no-seam case -/

/-- **A conjugator that meets `t` at no seam doubles it.**

If `k ≠ 1` and neither the first nor the last syllable of `k` lies in the factor
that `t` begins in, then nothing cancels in `t⁻¹ · k · t` at either seam, and
`|t⁻¹kt| = 2|t| + |k|`. -/
theorem wordNorm_conj_of_no_seam (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {t k : CoprodI G} (hk : k ≠ 1)
    (h1 : Word.fstIdx (Word.equiv t) ≠ Word.fstIdx (Word.equiv k))
    (h2 : Word.fstIdx (Word.equiv k⁻¹) ≠ Word.fstIdx (Word.equiv t)) :
    wordNorm (unionCarrier S) (t⁻¹ * k * t)
      = 2 * wordNorm (unionCarrier S) t + wordNorm (unionCarrier S) k := by
  have hA : wordNorm (unionCarrier S) (t⁻¹ * k)
      = wordNorm (unionCarrier S) t + wordNorm (unionCarrier S) k :=
    wordNorm_branch hS h1
  have hfst : Word.fstIdx (Word.equiv (t⁻¹ * k)⁻¹)
      = Word.fstIdx (Word.equiv k⁻¹) := by
    have hswap : ((t⁻¹ * k)⁻¹ : CoprodI G) = k⁻¹ * t := by group
    rw [hswap]
    exact fstIdx_equiv_inv_mul hk fun hcon => h1 hcon.symm
  have hB : wordNorm (unionCarrier S) (t⁻¹ * k * t)
      = wordNorm (unionCarrier S) (t⁻¹ * k) + wordNorm (unionCarrier S) t :=
    wordNorm_mul_of_seam hS (by rw [hfst]; exact h2)
  rw [hB, hA]
  omega

/-- **The no-seam case is excluded once `t` is long.** -/
theorem two_mul_wordNorm_le_conj (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {t k : CoprodI G} (hk : k ≠ 1)
    (h1 : Word.fstIdx (Word.equiv t) ≠ Word.fstIdx (Word.equiv k))
    (h2 : Word.fstIdx (Word.equiv k⁻¹) ≠ Word.fstIdx (Word.equiv t)) :
    2 * wordNorm (unionCarrier S) t
      ≤ wordNorm (unionCarrier S) (t⁻¹ * k * t) := by
  rw [wordNorm_conj_of_no_seam hS hk h1 h2]
  omega

/-- **The trichotomy the crossing estimate splits on.**  Either `t⁻¹kt` is at
least twice as long as `t` --- which `|t| ≥ R > ε/2` forbids --- or `k` meets the
leading factor of `t` at one of its two ends. -/
theorem conj_seam_cases (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {t k : CoprodI G} (hk : k ≠ 1) :
    2 * wordNorm (unionCarrier S) t ≤ wordNorm (unionCarrier S) (t⁻¹ * k * t)
      ∨ Word.fstIdx (Word.equiv t) = Word.fstIdx (Word.equiv k)
      ∨ Word.fstIdx (Word.equiv k⁻¹) = Word.fstIdx (Word.equiv t) := by
  by_cases h1 : Word.fstIdx (Word.equiv t) = Word.fstIdx (Word.equiv k)
  · exact Or.inr (Or.inl h1)
  · by_cases h2 : Word.fstIdx (Word.equiv k⁻¹) = Word.fstIdx (Word.equiv t)
    · exact Or.inr (Or.inr h2)
    · exact Or.inl (two_mul_wordNorm_le_conj hS hk h1 h2)

/-! ## 3.  The induction step -/

/-- **Peeling the leading syllable of the conjugator.**  The conjugate `t⁻¹kt`
does not change when the leading syllable `u` of `t` is moved onto `k`, and the
remaining conjugator has one syllable fewer.  This is what turns the two open
branches of `conj_seam_cases` into the same two branches at a shorter `t`. -/
theorem conj_peel {t : CoprodI G} {i : ι} {u : G i} (h : lead t = some ⟨i, u⟩)
    (k : CoprodI G) :
    ∃ t' : CoprodI G, sylLength t' + 1 = sylLength t ∧
      t⁻¹ * k * t
        = t'⁻¹ * ((CoprodI.of u)⁻¹ * k * CoprodI.of u) * t' := by
  obtain ⟨t', hteq, -, -, htlist⟩ := exists_split_toList h
  refine ⟨t', ?_, ?_⟩
  · simp only [sylLength, htlist, List.length_cons]
  · rw [hteq]
    group

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- The peeled conjugator is again nontrivial. -/
theorem conj_peel_ne_one {k : CoprodI G} {i : ι} {u : G i} (hk : k ≠ 1) :
    ((CoprodI.of u)⁻¹ * k * CoprodI.of u : CoprodI G) ≠ 1 := by
  intro hcon
  refine hk (eq_one_of_conj_eq_one (c := (CoprodI.of u)⁻¹) ?_)
  rwa [inv_inv]

end Crossing

end HullSCUnionGeometry
end GroupApproximation
