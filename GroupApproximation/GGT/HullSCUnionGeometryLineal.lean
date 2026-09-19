import GroupApproximation.GGT.HullSCUnionGeometryCrossing

/-!
# The lineal branch: a bounded conjugator, and the count

In the lineal configuration the element of the displacement set is written
`k = c · w · c⁻¹` with `w` cyclically reduced in the same factors that `c`'s ends
avoid.  The bound that matters is then on `|c|`, and it comes from `|k|` --- not
from `|t|`:

* `wordNorm_conj_conjugator` --- nothing cancels at either `c`/`w` seam, so
  `|c w c⁻¹| = 2|c| + |w|` exactly.  It is `wordNorm_conj_of_no_seam` read at
  `t = c⁻¹`; the concatenation lemma is what makes both seams visible from the
  front.
* `two_mul_wordNorm_le_conj_conjugator` and `wordNorm_le_conj_conjugator` --- so
  `|k| ≤ ε` gives `|c| ≤ ε/2` and `|w| ≤ ε`.
* `two_mul_sylLength_le_conj_conjugator` --- and therefore
  `2·(syllable count of c) ≤ |k|`, which is what bounds the conjugator to
  finitely many *prefixes* of `t`: prefixes are ordered by syllable count.
* `finite_of_conj_decomposition` --- the counting, in the only form that does not
  enumerate a ball: a displacement set all of whose elements are `c w c⁻¹` for
  `c` and `w` drawn from two *finite* sets is finite, of cardinality at most the
  product.  Hull's alphabets are infinite, so no step may bound a set of
  elements by its diameter, and this one does not.

## The residual

One structural clause, and it is the only thing between this module and the
crossing estimate:

> for `k` in the displacement set of a long `t`, and after `conj_peel` has been
> run, `k = c · w · c⁻¹` where `c` is a prefix of the normal form of `t` and `w`
> is either an element of a single factor or a power of the cyclic reduction of
> `t` (`FreeProductCyclic.exists_cyclicReduction` supplies that reduction).

Given it, the two finite sets of `finite_of_conj_decomposition` are: the prefixes
of `t` of syllable count at most `|k|/2`, of which there are at most `|k|/2 + 1`
because a prefix is determined by its syllable count; and, for `w`, either the
factor's own displacement set --- bounded by the factor's acylindricity, in the
conjugation form of `isAcylindrical_cayley_of_conjDisplacement` --- or the powers
`sᵐ` with `|m| ≤ |w| ≤ ε`, since a cyclically reduced `s` has `|sᵐ| ≥ |m|`.

What is *not* here is a prefix API: this development peels one syllable at a time
(`conj_peel`) and never names the `j`-th prefix of a word, so "a prefix is
determined by its syllable count" is not yet a theorem.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section Lineal

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-! ## 1.  A conjugator meeting its core at no seam -/

/-- **The double-seam lemma.**  If `w ≠ 1` and neither end of `w` lies in the
factor that `c` *ends* in, then nothing cancels at either seam of `c · w · c⁻¹`
and `|c w c⁻¹| = 2|c| + |w|`.

This is `wordNorm_conj_of_no_seam` at `t = c⁻¹`: the last syllable of `c` is the
first syllable of `c⁻¹`, so both seams are conditions on the front of `c⁻¹`. -/
theorem wordNorm_conj_conjugator (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {c w : CoprodI G} (hw : w ≠ 1)
    (h1 : Word.fstIdx (Word.equiv c⁻¹) ≠ Word.fstIdx (Word.equiv w))
    (h2 : Word.fstIdx (Word.equiv w⁻¹) ≠ Word.fstIdx (Word.equiv c⁻¹)) :
    wordNorm (unionCarrier S) (c * w * c⁻¹)
      = 2 * wordNorm (unionCarrier S) c + wordNorm (unionCarrier S) w := by
  have h : wordNorm (unionCarrier S) ((c⁻¹)⁻¹ * w * c⁻¹)
      = 2 * wordNorm (unionCarrier S) c⁻¹ + wordNorm (unionCarrier S) w :=
    wordNorm_conj_of_no_seam hS hw h1 h2
  rw [inv_inv, wordNorm_inv (isSymmetricGeneratingSet_unionCarrier hS)] at h
  exact h

/-- **The conjugator is bounded by the element**: `2|c| ≤ |c w c⁻¹|`. -/
theorem two_mul_wordNorm_le_conj_conjugator
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {c w : CoprodI G} (hw : w ≠ 1)
    (h1 : Word.fstIdx (Word.equiv c⁻¹) ≠ Word.fstIdx (Word.equiv w))
    (h2 : Word.fstIdx (Word.equiv w⁻¹) ≠ Word.fstIdx (Word.equiv c⁻¹)) :
    2 * wordNorm (unionCarrier S) c
      ≤ wordNorm (unionCarrier S) (c * w * c⁻¹) := by
  rw [wordNorm_conj_conjugator hS hw h1 h2]
  omega

/-- **The core is bounded by the element**: `|w| ≤ |c w c⁻¹|`. -/
theorem wordNorm_le_conj_conjugator (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {c w : CoprodI G} (hw : w ≠ 1)
    (h1 : Word.fstIdx (Word.equiv c⁻¹) ≠ Word.fstIdx (Word.equiv w))
    (h2 : Word.fstIdx (Word.equiv w⁻¹) ≠ Word.fstIdx (Word.equiv c⁻¹)) :
    wordNorm (unionCarrier S) w ≤ wordNorm (unionCarrier S) (c * w * c⁻¹) := by
  rw [wordNorm_conj_conjugator hS hw h1 h2]
  omega

/-- **The conjugator has boundedly many syllables.**  A syllable costs at least
one letter, so `2·sylLength c ≤ |c w c⁻¹|`.  This is what confines `c` to
finitely many prefixes of `t`, which are ordered by syllable count. -/
theorem two_mul_sylLength_le_conj_conjugator
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {c w : CoprodI G} (hw : w ≠ 1)
    (h1 : Word.fstIdx (Word.equiv c⁻¹) ≠ Word.fstIdx (Word.equiv w))
    (h2 : Word.fstIdx (Word.equiv w⁻¹) ≠ Word.fstIdx (Word.equiv c⁻¹)) :
    2 * sylLength c ≤ wordNorm (unionCarrier S) (c * w * c⁻¹) := by
  have hsyl := sylLength_le_wordNorm hS c
  have hbound := two_mul_wordNorm_le_conj_conjugator hS hw h1 h2
  omega

end Lineal

/-! ## 2.  The count, without enumerating a ball -/

section Counting

variable {H : Type*} [Group H]

/-- **A displacement set whose elements are conjugates from two finite sets is
finite**, with cardinality at most the product.

This is the only counting step the free product estimate may use: Hull's
alphabets are infinite, so a ball is infinite and no set of elements may be
bounded by its diameter.  Here the bound comes from the *shape* of the elements
--- a conjugator drawn from finitely many prefixes and a core drawn from finitely
many candidates --- and never from a radius. -/
theorem finite_of_conj_decomposition {D : Set H} (P Q : Finset H)
    (hD : ∀ k ∈ D, ∃ c ∈ P, ∃ w ∈ Q, k = c * w * c⁻¹) :
    D.Finite ∧ D.ncard ≤ P.card * Q.card := by
  classical
  have hsub : D ⊆ ↑((P ×ˢ Q).image fun p : H × H => p.1 * p.2 * p.1⁻¹) := by
    intro k hk
    obtain ⟨c, hc, w, hw, rfl⟩ := hD k hk
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨(c, w), Finset.mem_product.mpr ⟨hc, hw⟩, rfl⟩)
  refine ⟨Set.Finite.subset (Finset.finite_toSet _) hsub, ?_⟩
  calc D.ncard
      ≤ (↑((P ×ˢ Q).image fun p : H × H => p.1 * p.2 * p.1⁻¹) : Set H).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((P ×ˢ Q).image fun p : H × H => p.1 * p.2 * p.1⁻¹).card :=
        Set.ncard_coe_finset _
    _ ≤ (P ×ˢ Q).card := Finset.card_image_le
    _ = P.card * Q.card := by rw [Finset.card_product]

end Counting

end HullSCUnionGeometry
end GroupApproximation
