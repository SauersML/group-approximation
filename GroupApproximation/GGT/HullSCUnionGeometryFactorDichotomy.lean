import GroupApproximation.GGT.HullSCUnionGeometrySyllableCount

/-!
# A long syllable forces its own factor

The branch of the acylindricity clause that the syllable count does not reach is
the one where `t` has few syllables and large word length --- one letter of a
Hull alphabet is arbitrarily long, so `R ≤ |t|` does not bound `sylLength t`
from below.  There the length of `t` sits inside single syllables, and the
statement that replaces the prefix count is this dichotomy:

    either `k` is a single letter of the factor of `x`,
    or `2 |x| ≤ |(of x)⁻¹ k (of x)| + |k|` .

So conjugating by a long letter is expensive unless `k` lies in that letter's
own factor, where the factor's own acylindricity takes over.

## The shape of the proof

Everything reduces to one estimate, proved once and used twice.  If the *last*
syllable of `k` avoids the factor of `x`, the right-hand seam of
`(of x)⁻¹ k (of x)` is free, so its length is `|(of x)⁻¹ k| + |x|`, and
`|x| ≤ |(of x)⁻¹ k| + |k|` is the triangle inequality.  That is
`two_mul_wordNorm_le_conj_single_of_back`; reading it at `k⁻¹` gives the same
conclusion when the *first* syllable of `k` avoids the factor, because
`((of x)⁻¹ k (of x))⁻¹ = (of x)⁻¹ k⁻¹ (of x)`.

What is left is `k` with both ends in the factor of `x`.  Peeling both of them
writes `k = of z * k₁ * of w` with `z, w` in that factor and `k₁` avoiding it at
both ends --- `k₁ = 1` is exactly the first alternative of the dichotomy --- and
then no seam of `of (x⁻¹ z) * k₁ * of (w x)` cancels, so its length is
`|x⁻¹ z| + |k₁| + |w x|`, and two triangle inequalities in the factor,
`|x| ≤ |z| + |x⁻¹ z|` and `|x| ≤ |w| + |w x|`, finish it.

`exists_back_split` is the peel at the back: `Word.equiv` is head-oriented, so
the last syllable of `g` is read as the first syllable of `g⁻¹` and carried back
by `invList`.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

section Dichotomy

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-! ## 1.  Two readings of a concatenation -/

/-- **The union word length splits along a concatenation of reduced blocks.** -/
theorem wordNorm_of_toList_append (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {x c u : CoprodI G}
    (h : (Word.equiv x).toList
      = (Word.equiv c).toList ++ (Word.equiv u).toList) :
    wordNorm (unionCarrier S) x
      = wordNorm (unionCarrier S) c + wordNorm (unionCarrier S) u := by
  rw [wordNorm_eq_syllableNorm hS, wordNorm_eq_syllableNorm hS,
    wordNorm_eq_syllableNorm hS]
  show wsum S (Word.equiv x) = wsum S (Word.equiv c) + wsum S (Word.equiv u)
  simp only [wsum, h, List.map_append, List.sum_append]

/-- **The first index survives a free seam.** -/
theorem fstIdx_mul_of_seam {u y : CoprodI G} (hu : u ≠ 1)
    (h : Word.fstIdx (Word.equiv u⁻¹) ≠ Word.fstIdx (Word.equiv y)) :
    Word.fstIdx (Word.equiv (u * y)) = Word.fstIdx (Word.equiv u) :=
  fstIdx_of_toList_append (toList_equiv_mul_of_seam h)
    (toList_ne_nil_of_ne_one hu)

/-! ## 2.  Peeling the last syllable -/

/-- **The back split.**  An element whose last syllable lies in the factor `q`
is a shorter element times one letter of `q`, and the reduced words
concatenate. -/
theorem exists_back_split {g : CoprodI G} {q : ι}
    (h : Word.fstIdx (Word.equiv g⁻¹) = some q) :
    ∃ (w : G q) (g₁ : CoprodI G), g = g₁ * CoprodI.of w ∧ w ≠ 1 ∧
      Word.fstIdx (Word.equiv g₁⁻¹) ≠ some q ∧
      (Word.equiv g).toList
        = (Word.equiv g₁).toList
          ++ (Word.equiv (CoprodI.of w : CoprodI G)).toList := by
  obtain ⟨y, hy⟩ := exists_lead_index h
  obtain ⟨h₀, hgeq, hy1, hh0idx, hglist⟩ := exists_split_toList hy
  have hinv : ((CoprodI.of y : CoprodI G)⁻¹) = CoprodI.of y⁻¹ :=
    (map_inv (CoprodI.of : G q →* CoprodI G) y).symm
  have hgi : g = (CoprodI.of y * h₀)⁻¹ := by rw [← hgeq, inv_inv]
  refine ⟨y⁻¹, h₀⁻¹, ?_, inv_ne_one.mpr hy1, ?_, ?_⟩
  · rw [hgi, mul_inv_rev, hinv]
  · rw [inv_inv]
    exact hh0idx
  · have hg : (Word.equiv g).toList
        = CoprodIWordInverse.invList ((Word.equiv g⁻¹).toList) := by
      have hh := toList_equiv_inv g⁻¹
      rwa [inv_inv] at hh
    have hcons : (Word.equiv g⁻¹).toList
        = (Word.equiv (CoprodI.of y : CoprodI G)).toList
          ++ (Word.equiv h₀).toList := by
      rw [hglist, toList_equiv_of_single hy1, List.singleton_append]
    rw [hg, hcons, invList_append, ← toList_equiv_inv, ← toList_equiv_inv, hinv]

/-! ## 3.  One free end -/

/-- **A free end at the back.**  If the last syllable of `k` avoids the factor
of `x`, conjugating by `of x` costs a whole `x` there. -/
theorem two_mul_wordNorm_le_conj_single_of_back
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {q : ι} (x : G q)
    {k : CoprodI G} (hk : k ≠ 1)
    (hb : Word.fstIdx (Word.equiv k⁻¹) ≠ some q) :
    2 * wordNorm (S q) x
      ≤ wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k * CoprodI.of x)
        + wordNorm (unionCarrier S) k := by
  have hcar := isSymmetricGeneratingSet_unionCarrier hS
  by_cases hx : x = 1
  · rw [hx, wordNorm_one]
    omega
  have hxidx : Word.fstIdx (Word.equiv (CoprodI.of x : CoprodI G)) = some q :=
    fstIdx_of_single hx
  -- the outer right seam is free
  have hseam : Word.fstIdx (Word.equiv ((CoprodI.of x)⁻¹ * k)⁻¹)
      ≠ Word.fstIdx (Word.equiv (CoprodI.of x : CoprodI G)) := by
    rw [hxidx]
    have hrw : (((CoprodI.of x)⁻¹ * k)⁻¹ : CoprodI G)
        = k⁻¹ * CoprodI.of x := by
      rw [mul_inv_rev, inv_inv]
    rw [hrw]
    by_cases hf : Word.fstIdx (Word.equiv k) = some q
    · obtain ⟨z, hz⟩ := exists_lead_index hf
      obtain ⟨k₀, hkeq, hz1, hk0idx, -⟩ := exists_split_toList hz
      have hzinv : ((CoprodI.of z : CoprodI G)⁻¹) = CoprodI.of z⁻¹ :=
        (map_inv (CoprodI.of : G q →* CoprodI G) z).symm
      have hkinv : (k⁻¹ : CoprodI G) = k₀⁻¹ * CoprodI.of z⁻¹ := by
        rw [hkeq, mul_inv_rev, hzinv]
      have hk0 : k₀ ≠ 1 := by
        intro h1
        rw [h1, mul_one] at hkeq
        rw [hkeq, hzinv] at hb
        exact hb (fstIdx_of_single (inv_ne_one.mpr hz1))
      have hk0seam : Word.fstIdx (Word.equiv (k₀⁻¹)⁻¹)
          ≠ Word.fstIdx (Word.equiv (CoprodI.of z⁻¹ : CoprodI G)) := by
        rw [inv_inv, fstIdx_of_single (inv_ne_one.mpr hz1)]
        exact hk0idx
      have hk0b : Word.fstIdx (Word.equiv k₀⁻¹)
          = Word.fstIdx (Word.equiv k⁻¹) := by
        rw [hkinv]
        exact (fstIdx_mul_of_seam (inv_ne_one.mpr hk0) hk0seam).symm
      have hprod : (k⁻¹ * CoprodI.of x : CoprodI G)
          = k₀⁻¹ * CoprodI.of (z⁻¹ * x) := by
        rw [hkinv, map_mul, mul_assoc]
      rw [hprod]
      by_cases hzx : (z⁻¹ * x : G q) = 1
      · rw [hzx, map_one, mul_one, hk0b]
        exact hb
      · have hseam2 : Word.fstIdx (Word.equiv (k₀⁻¹)⁻¹)
            ≠ Word.fstIdx (Word.equiv (CoprodI.of (z⁻¹ * x) : CoprodI G)) := by
          rw [inv_inv, fstIdx_of_single hzx]
          exact hk0idx
        rw [fstIdx_mul_of_seam (inv_ne_one.mpr hk0) hseam2, hk0b]
        exact hb
    · have hseam3 : Word.fstIdx (Word.equiv (k⁻¹)⁻¹)
          ≠ Word.fstIdx (Word.equiv (CoprodI.of x : CoprodI G)) := by
        rw [inv_inv, hxidx]
        exact hf
      rw [fstIdx_mul_of_seam (inv_ne_one.mpr hk) hseam3]
      exact hb
  have hsplit : wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k * CoprodI.of x)
      = wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k)
        + wordNorm (unionCarrier S) (CoprodI.of x) :=
    wordNorm_mul_of_seam hS hseam
  have htri : wordNorm (unionCarrier S) (CoprodI.of x)
      ≤ wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k)
        + wordNorm (unionCarrier S) k := by
    have h2 := wordNorm_mul_le hcar ((CoprodI.of x)⁻¹ * k) k⁻¹
    have h1 : ((((CoprodI.of x)⁻¹ * k) * k⁻¹ : CoprodI G))
        = (CoprodI.of x)⁻¹ := by group
    rw [h1, wordNorm_inv hcar, wordNorm_inv hcar] at h2
    exact h2
  have hxnorm : wordNorm (unionCarrier S) (CoprodI.of x) = wordNorm (S q) x :=
    wordNorm_of_single_eq hS x
  rw [← hxnorm]
  omega

/-- **A free end at the front**, read at `k⁻¹`. -/
theorem two_mul_wordNorm_le_conj_single_of_front
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {q : ι} (x : G q)
    {k : CoprodI G} (hk : k ≠ 1)
    (hf : Word.fstIdx (Word.equiv k) ≠ some q) :
    2 * wordNorm (S q) x
      ≤ wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k * CoprodI.of x)
        + wordNorm (unionCarrier S) k := by
  have hcar := isSymmetricGeneratingSet_unionCarrier hS
  have hb : Word.fstIdx (Word.equiv (k⁻¹)⁻¹) ≠ some q := by
    rw [inv_inv]
    exact hf
  have h := two_mul_wordNorm_le_conj_single_of_back hS x
    (inv_ne_one.mpr hk) hb
  have h1 : wordNorm (unionCarrier S) k⁻¹ = wordNorm (unionCarrier S) k := by
    rw [wordNorm_inv hcar]
  have h2 : wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k⁻¹ * CoprodI.of x)
      = wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k * CoprodI.of x) := by
    have hrw : ((CoprodI.of x)⁻¹ * k⁻¹ * CoprodI.of x : CoprodI G)
        = ((CoprodI.of x)⁻¹ * k * CoprodI.of x)⁻¹ := by group
    rw [hrw, wordNorm_inv hcar]
  rw [h1, h2] at h
  exact h

/-! ## 4.  The dichotomy -/

/-- **A long letter forces its own factor.**  Either `k` is a single letter of
the factor of `x`, or conjugating by `of x` costs `2 |x|` up to `|k|`. -/
theorem conj_single_dichotomy (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {q : ι} (x : G q) (k : CoprodI G) :
    (∃ γ : G q, k = CoprodI.of γ) ∨
      2 * wordNorm (S q) x
        ≤ wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k * CoprodI.of x)
          + wordNorm (unionCarrier S) k := by
  by_cases hk : k = 1
  · exact Or.inl ⟨1, by rw [hk, map_one]⟩
  by_cases hf : Word.fstIdx (Word.equiv k) = some q
  · by_cases hb : Word.fstIdx (Word.equiv k⁻¹) = some q
    · -- both ends lie in the factor of `x`
      obtain ⟨z, hz⟩ := exists_lead_index hf
      obtain ⟨k₀, hkeq, hz1, hk0idx, -⟩ := exists_split_toList hz
      by_cases hk0 : k₀ = 1
      · exact Or.inl ⟨z, by rw [hkeq, hk0, mul_one]⟩
      have hzinv : ((CoprodI.of z : CoprodI G)⁻¹) = CoprodI.of z⁻¹ :=
        (map_inv (CoprodI.of : G q →* CoprodI G) z).symm
      have hkinv : (k⁻¹ : CoprodI G) = k₀⁻¹ * CoprodI.of z⁻¹ := by
        rw [hkeq, mul_inv_rev, hzinv]
      have hk0seam : Word.fstIdx (Word.equiv (k₀⁻¹)⁻¹)
          ≠ Word.fstIdx (Word.equiv (CoprodI.of z⁻¹ : CoprodI G)) := by
        rw [inv_inv, fstIdx_of_single (inv_ne_one.mpr hz1)]
        exact hk0idx
      have hk0b : Word.fstIdx (Word.equiv k₀⁻¹) = some q := by
        rw [← hb, hkinv]
        exact (fstIdx_mul_of_seam (inv_ne_one.mpr hk0) hk0seam).symm
      obtain ⟨w, k₁, hk0eq, hw1, hk1b, hk0list⟩ := exists_back_split hk0b
      have hk1ne : k₁ ≠ 1 := by
        intro h1
        rw [h1, one_mul] at hk0eq
        rw [hk0eq, fstIdx_of_single hw1] at hk0idx
        exact hk0idx rfl
      have hk1f : Word.fstIdx (Word.equiv k₁) ≠ some q := by
        rw [← fstIdx_of_toList_append hk0list (toList_ne_nil_of_ne_one hk1ne)]
        exact hk0idx
      -- the two seams at `k₁`
      have hback : ∀ v : G q, wordNorm (unionCarrier S) (k₁ * CoprodI.of v)
          = wordNorm (unionCarrier S) k₁ + wordNorm (S q) v := by
        intro v
        by_cases hv : v = 1
        · rw [hv, map_one, mul_one, wordNorm_one]
          omega
        · have hseam : Word.fstIdx (Word.equiv k₁⁻¹)
              ≠ Word.fstIdx (Word.equiv (CoprodI.of v : CoprodI G)) := by
            rw [fstIdx_of_single hv]
            exact hk1b
          rw [wordNorm_mul_of_seam hS hseam, wordNorm_of_single_eq hS]
      have hbackidx : ∀ v : G q,
          Word.fstIdx (Word.equiv (k₁ * CoprodI.of v)) ≠ some q := by
        intro v
        by_cases hv : v = 1
        · rw [hv, map_one, mul_one]
          exact hk1f
        · have hseam : Word.fstIdx (Word.equiv k₁⁻¹)
              ≠ Word.fstIdx (Word.equiv (CoprodI.of v : CoprodI G)) := by
            rw [fstIdx_of_single hv]
            exact hk1b
          rw [fstIdx_mul_of_seam hk1ne hseam]
          exact hk1f
      have hfront : ∀ (v : G q) (g : CoprodI G),
          Word.fstIdx (Word.equiv g) ≠ some q →
          wordNorm (unionCarrier S) (CoprodI.of v * g)
            = wordNorm (S q) v + wordNorm (unionCarrier S) g := by
        intro v g hg
        by_cases hv : v = 1
        · rw [hv, map_one, one_mul, wordNorm_one]
          omega
        · exact wordNorm_of_mul hS hv hg
      -- the length of the conjugate, and of `k`
      have hconj : (CoprodI.of x)⁻¹ * k * CoprodI.of x
          = CoprodI.of (x⁻¹ * z) * k₁ * CoprodI.of (w * x) := by
        rw [hkeq, hk0eq, map_mul, map_mul, map_inv]
        group
      have hA : wordNorm (unionCarrier S) ((CoprodI.of x)⁻¹ * k * CoprodI.of x)
          = wordNorm (S q) (x⁻¹ * z) + wordNorm (unionCarrier S) k₁
            + wordNorm (S q) (w * x) := by
        rw [hconj, mul_assoc,
          hfront (x⁻¹ * z) (k₁ * CoprodI.of (w * x)) (hbackidx (w * x)),
          hback (w * x)]
        omega
      have hknorm : wordNorm (unionCarrier S) k
          = wordNorm (S q) z + wordNorm (unionCarrier S) k₀ := by
        rw [hkeq]
        exact wordNorm_of_mul hS hz1 hk0idx
      have hk0norm : wordNorm (unionCarrier S) k₀
          = wordNorm (unionCarrier S) k₁ + wordNorm (S q) w := by
        rw [wordNorm_of_toList_append hS hk0list, wordNorm_of_single_eq hS]
      -- two triangle inequalities inside the factor
      have htri1 : wordNorm (S q) x
          ≤ wordNorm (S q) z + wordNorm (S q) (x⁻¹ * z) := by
        have h2 := wordNorm_mul_le (hS q) z ((x⁻¹ * z)⁻¹)
        rw [wordNorm_inv (hS q)] at h2
        have h1 : (z * (x⁻¹ * z)⁻¹ : G q) = x := by group
        rw [h1] at h2
        exact h2
      have htri2 : wordNorm (S q) x
          ≤ wordNorm (S q) w + wordNorm (S q) (w * x) := by
        have h2 := wordNorm_mul_le (hS q) w⁻¹ (w * x)
        rw [wordNorm_inv (hS q)] at h2
        have h1 : (w⁻¹ * (w * x) : G q) = x := by group
        rw [h1] at h2
        exact h2
      exact Or.inr (by omega)
    · exact Or.inr (two_mul_wordNorm_le_conj_single_of_back hS x hk hb)
  · exact Or.inr (two_mul_wordNorm_le_conj_single_of_front hS x hk hf)

end Dichotomy

end HullSCUnionGeometry
end GroupApproximation
