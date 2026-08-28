import GroupApproximation.GGT.HullSCUnionGeometryLongSyllable

/-!
# The factor-conjugate branch, closed

`exists_factor_displacement` produced, for `k = a⁻¹ (of x) a`, a corrected
conjugator `a'` with `2|a'| ≤ |k|` and a factor element `σ` with
`t = a'⁻¹ · (of σ) · b'`.  Bounding `|a'|` is not by itself a count: Hull's
alphabets are infinite, so a ball of radius `|k|` contains infinitely many
elements.

What closes the branch is that `a'⁻¹` is a **prefix of `t`**.  Both seams of
`t = a'⁻¹ · (of σ) · b'` are seam-free by construction --- `a'` and `b'` avoid the
factor `i`, and `of σ` lies in it --- so `toList_equiv_mul_of_seam`, applied
twice, says the reduced word of `t` is the concatenation

    t‾  =  (a'⁻¹)‾ ++ [⟨i,σ⟩] ++ b'‾ .

So `a'⁻¹` is a syllable prefix of `t` of syllable count at most `|k|/2`, and
`finite_syllablePrefix` says there are at most `|k|/2 + 1` of those.  Together
with the factor's own acylindricity at `σ` --- which
`exists_factor_displacement` already set up --- and
`finite_of_conj_decomposition`, that is the count.

`exists_factor_conj_prefix` packages it.  The hypothesis is the only thing the
regime needs: `|k| + |t⁻¹kt| < 2|t|`, which is exactly what makes `σ ≠ 1`, hence
what makes the middle syllable real.  For `|t| ≥ R > ε` it holds automatically.

The remaining branch is the lineal one, and it is now the only one.  It needs the
free-product conjugacy theorem for cyclically reduced words --- `s'` a cyclic
permutation of `s`, and the conjugator a prefix times a power --- which
`Algebra/FreeProductConjugacy.lean` does *not* contain: that module proves the
syllable length of the cyclic reduction is a conjugacy invariant
(`length_eq_of_conj`), that a cyclically reduced word is shortest in its class
(`length_le_sylLength_conj`), and that powers have proportional length
(`sylLength_npow`), but not the classification of the conjugator.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section FactorBranch

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-- **The conjugator of a factor-conjugate displacement is a prefix of `t`.**

For `k = a⁻¹ (of x) a` with `|k| + |t⁻¹kt| < 2|t|` there are a prefix `c` of `t`,
a letter `x'` of the factor and a factor element `σ` with

* `k = c · (of x') · c⁻¹` and `2·sylLength c ≤ |k|`;
* `|x'|ᵢ ≤ |k|` and `|σ⁻¹x'σ|ᵢ ≤ |t⁻¹kt|`.

So `c` ranges over the prefixes of `t` of bounded syllable count
(`finite_syllablePrefix`) and `x'` over the factor's conjugation displacement set
at `σ`, and `finite_of_conj_decomposition` turns the two into a count. -/
theorem exists_factor_conj_prefix (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {i : ι} {x : G i} (hx : x ≠ 1) (a t : CoprodI G)
    (ht : wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a)
        + wordNorm (unionCarrier S) (t⁻¹ * (a⁻¹ * CoprodI.of x * a) * t)
        < 2 * wordNorm (unionCarrier S) t) :
    ∃ (c : CoprodI G) (x' σ : G i),
      IsSyllablePrefix c t ∧ x' ≠ 1 ∧
      a⁻¹ * CoprodI.of x * a = c * CoprodI.of x' * c⁻¹ ∧
      2 * sylLength c ≤ wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a) ∧
      wordNorm (S i) x'
        ≤ wordNorm (unionCarrier S) (a⁻¹ * CoprodI.of x * a) ∧
      wordNorm (S i) (σ⁻¹ * x' * σ)
        ≤ wordNorm (unionCarrier S) (t⁻¹ * (a⁻¹ * CoprodI.of x * a) * t) := by
  obtain ⟨y, a', haeq, ha'idx, hxy, hknorm⟩ := exists_conj_normal_form hS hx a
  obtain ⟨w, b', hbeq, hb'idx, -, htnorm⟩ := exists_conj_normal_form hS hx (a * t)
  have hC := isSymmetricGeneratingSet_unionCarrier hS
  have hconj : t⁻¹ * (a⁻¹ * CoprodI.of x * a) * t
      = (a * t)⁻¹ * CoprodI.of x * (a * t) := by group
  have hteq : t = a'⁻¹ * CoprodI.of (y⁻¹ * w) * b' := by
    have h1 : t = a⁻¹ * (a * t) := by group
    rw [h1, hbeq, haeq, map_mul, map_inv]
    group
  have hσ : (y⁻¹ * w : G i) ≠ 1 := by
    intro hcon
    have h0 : t = a'⁻¹ * b' := by rw [hteq, hcon, map_one, mul_one]
    have h1 : wordNorm (unionCarrier S) t
        ≤ wordNorm (unionCarrier S) a' + wordNorm (unionCarrier S) b' := by
      have h2 := wordNorm_mul_le hC a'⁻¹ b'
      have h3 := wordNorm_inv hC a'
      rw [h0]
      omega
    rw [hconj] at ht
    omega
  have hσfst : Word.fstIdx (Word.equiv (CoprodI.of (y⁻¹ * w) : CoprodI G))
      = some i := fstIdx_of_single hσ
  have hseam1 : (Word.equiv (a'⁻¹ * CoprodI.of (y⁻¹ * w))).toList
      = (Word.equiv a'⁻¹).toList
        ++ (Word.equiv (CoprodI.of (y⁻¹ * w) : CoprodI G)).toList := by
    refine toList_equiv_mul_of_seam ?_
    rw [inv_inv, hσfst]
    exact ha'idx
  have hfstm : Word.fstIdx (Word.equiv ((a'⁻¹ * CoprodI.of (y⁻¹ * w))⁻¹))
      = some i := by
    have hrw : ((a'⁻¹ * CoprodI.of (y⁻¹ * w))⁻¹ : CoprodI G)
        = CoprodI.of (y⁻¹ * w)⁻¹ * a' := by
      rw [mul_inv_rev, inv_inv, ← map_inv]
    rw [hrw]
    exact fstIdx_of_mul (inv_ne_one.mpr hσ) ha'idx
  have hseam2 : (Word.equiv t).toList
      = (Word.equiv (a'⁻¹ * CoprodI.of (y⁻¹ * w))).toList
        ++ (Word.equiv b').toList := by
    rw [hteq]
    refine toList_equiv_mul_of_seam ?_
    rw [hfstm]
    exact fun hcon => hb'idx hcon.symm
  refine ⟨a'⁻¹, y⁻¹ * x * y, y⁻¹ * w, ?_, hxy, ?_, ?_, ?_, ?_⟩
  · refine ⟨(Word.equiv (CoprodI.of (y⁻¹ * w) : CoprodI G)).toList
      ++ (Word.equiv b').toList, ?_⟩
    rw [← List.append_assoc, ← hseam1, ← hseam2]
  · rw [haeq, inv_inv, map_mul, map_mul, map_inv]
    group
  · have h3 : sylLength a'⁻¹ = sylLength a' := sylLength_inv a'
    have h4 := sylLength_le_wordNorm hS a'
    omega
  · omega
  · have hx'' : ((y⁻¹ * w)⁻¹ * (y⁻¹ * x * y) * (y⁻¹ * w) : G i)
        = w⁻¹ * x * w := by group
    rw [hx'', hconj]
    omega

end FactorBranch

end HullSCUnionGeometry
end GroupApproximation
