import GroupApproximation.GGT.HullSCUnionGeometryPrefix
import GroupApproximation.Algebra.FreeProductConjugacy

/-!
# The elliptic dichotomy

An element conjugate into a single factor is elliptic on the Bass-Serre tree, and
the tree argument for it is: it fixes a unique vertex `v` (trivial edge
stabilisers), so `d(y, k·y) = 2·d(y,v)` for every `y`, and the triangle
inequality at `y = 1` and `y = t` bounds `d(1,t)`.

None of that has to be built.  The conjugator seam lemmas already say it, and
the statement they say it in is sharper.  Write `k = a⁻¹ · of x · a`; then
`t⁻¹ k t = (a t)⁻¹ · of x · (a t)`, so `t = a⁻¹ · (a t)` and the two hypotheses
`|k| ≤ ε`, `|t⁻¹kt| ≤ ε` are two instances of one inequality:

  `two_mul_sylLength_le_conj_single` :  `2·sylLength a ≤ |a⁻¹ (of x) a| + 2`.

That is the whole content, and it is `wordNorm_conj_of_no_seam` plus one peel.
Either the normal form of `a` avoids the factor `i` of `x` --- and then nothing
cancels at either seam, `|a⁻¹ (of x) a| = 2|a| + |x|`, and a syllable costs a
letter --- or it begins in `i`, in which case exactly *one* syllable can be
absorbed into `x` (two consecutive syllables of a reduced word never share a
factor), and the first case applies to what is left.  The `+ 2` is that one
syllable.

`sylLength_le_of_conj_into_factor` adds the two instances:

  `2·sylLength t ≤ |k| + |t⁻¹kt| + 4` ,

so `sylLength t ≤ ε + 2`.  **For `sylLength t > ε + 2` the displacement set of
`t` contains no element conjugate into a factor at all** --- which is the
dichotomy, with an explicit constant and no tree.

The remaining branch is the lineal one: `k` not conjugate into a factor, i.e.
cyclically reduced with its two ends in different factors
(`FreeProductCyclic.exists_cyclicReduction` splits exactly these two cases).
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section Elliptic

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-! ## 1.  A single syllable -/

/-- The normal form of a nontrivial letter is that one letter. -/
theorem toList_equiv_of_single {i : ι} {x : G i} (hx : x ≠ 1) :
    (Word.equiv (CoprodI.of x : CoprodI G)).toList = [⟨i, x⟩] := by
  have h1 : Word.fstIdx (Word.equiv (1 : CoprodI G)) ≠ some i := by
    simp [Word.fstIdx, equiv_one, Word.empty]
  have h := toList_equiv_of_mul hx h1
  rw [mul_one] at h
  rw [h, equiv_one]; rfl

theorem of_ne_one {i : ι} {x : G i} (hx : x ≠ 1) :
    (CoprodI.of x : CoprodI G) ≠ 1 := by
  intro h
  have hl := toList_equiv_of_single hx
  rw [h, equiv_one] at hl
  simp [Word.empty] at hl

theorem fstIdx_of_single {i : ι} {x : G i} (hx : x ≠ 1) :
    Word.fstIdx (Word.equiv (CoprodI.of x : CoprodI G)) = some i := by
  simp [Word.fstIdx, toList_equiv_of_single hx]

/-! ## 2.  Conjugating one syllable -/

/-- **No cancellation at either seam.**  If the normal form of `a` avoids the
factor of `x`, then `|a⁻¹ (of x) a| = 2|a| + |x|`. -/
theorem wordNorm_conj_single_of_fstIdx_ne
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {i : ι} {x : G i} (hx : x ≠ 1)
    {a : CoprodI G} (ha : Word.fstIdx (Word.equiv a) ≠ some i) :
    wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a)
      = 2 * wordNorm (unionCarrier S) a
        + wordNorm (unionCarrier S) (CoprodI.of x) := by
  refine wordNorm_conj_of_no_seam hS (of_ne_one hx) ?_ ?_
  · rw [fstIdx_of_single hx]
    exact ha
  · have hinv : ((CoprodI.of x : CoprodI G)⁻¹) = CoprodI.of x⁻¹ :=
      (map_inv (CoprodI.of : G i →* CoprodI G) x).symm
    rw [hinv, fstIdx_of_single (inv_ne_one.mpr hx)]
    exact fun hcon => ha hcon.symm

/-- **The elliptic estimate.**  `2·sylLength a ≤ |a⁻¹ (of x) a| + 2`: at most one
syllable of `a` can be absorbed into `x`, because two consecutive syllables of a
reduced word never lie in the same factor. -/
theorem two_mul_sylLength_le_conj_single
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {i : ι} {x : G i} (hx : x ≠ 1)
    (a : CoprodI G) :
    2 * sylLength a
      ≤ wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a) + 2 := by
  by_cases ha : Word.fstIdx (Word.equiv a) = some i
  · obtain ⟨y, hy⟩ := exists_lead_index ha
    obtain ⟨a', haeq, -, ha'idx, halist⟩ := exists_split_toList hy
    have hxy : (y⁻¹ * x * y : G i) ≠ 1 := by
      intro hcon
      refine hx ?_
      have hx' : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      rw [hx', hcon]
      group
    have heq : a⁻¹ * CoprodI.of x * a
        = a'⁻¹ * CoprodI.of (y⁻¹ * x * y) * a' := by
      rw [haeq, map_mul, map_mul, map_inv]
      group
    have hlen : sylLength a = sylLength a' + 1 := by
      simp only [sylLength, halist, List.length_cons]
    have hsyl := sylLength_le_wordNorm hS a'
    rw [heq, wordNorm_conj_single_of_fstIdx_ne hS hxy ha'idx]
    omega
  · have hsyl := sylLength_le_wordNorm hS a
    rw [wordNorm_conj_single_of_fstIdx_ne hS hx ha]
    omega

/-! ## 3.  The dichotomy -/

/-- **The elliptic dichotomy.**  For `k = a⁻¹ (of x) a` one has
`t⁻¹ k t = (a t)⁻¹ (of x) (a t)` and `t = a⁻¹ (a t)`, so the two displacement
bounds add to a bound on the syllable count of `t`:

    `2·sylLength t ≤ |k| + |t⁻¹ k t| + 4` .

Hence for `sylLength t > ε + 2` no element of the displacement set of `t` is
conjugate into a factor. -/
theorem sylLength_le_of_conj_into_factor
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {i : ι} {x : G i} (hx : x ≠ 1)
    (a b : CoprodI G) :
    2 * sylLength (a⁻¹ * b)
      ≤ wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a)
        + wordNorm (unionCarrier S) (b⁻¹ * CoprodI.of x * b) + 4 := by
  have h1 := two_mul_sylLength_le_conj_single hS hx a
  have h2 := two_mul_sylLength_le_conj_single hS hx b
  have h3 : sylLength (a⁻¹ * b) ≤ sylLength a + sylLength b := by
    have h4 := sylLength_mul_le a⁻¹ b
    rwa [sylLength_inv] at h4
  omega

end Elliptic

end HullSCUnionGeometry
end GroupApproximation
