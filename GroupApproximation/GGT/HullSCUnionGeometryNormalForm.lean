import GroupApproximation.Algebra.FreeProductUnionNorm

/-!
# Cancellation in a free product spelled over a union alphabet

`Algebra/FreeProductUnionNorm.lean` proves the syllable-sum formula
`|g| = Σ |gₖ|` for the alphabet `unionCarrier S` of `CoprodI G`, whose letters
are the letters of each factor alphabet `S i` inside its own factor.  That
formula measures *one* element.  Everything geometric measures *two*, through
`d(x,y) = |x⁻¹y|`, and so needs to know how much of `x` cancels against `y`.

This module answers that, in the only three shapes the four-point condition of
`GGT/HullSCUnionGeometryFourPoint.lean` consumes.  Write `|·|` for the union
word length and let `x`, `y` have leading syllables `⟨i,u⟩`, `⟨j,v⟩`.

* `wordNorm_branch` --- if `i ≠ j`, or one of the two elements is trivial, then
  `|x⁻¹y| = |x| + |y|`: nothing cancels.
* `wordNorm_branch_same` --- if `i = j` and `u ≠ v`, then
  `|x⁻¹y| + |u|ᵢ + |v|ᵢ = |x| + |y| + |u⁻¹v|ᵢ`: exactly the two leading
  syllables merge, into the single syllable `u⁻¹v`.
* `wordNorm_same_lead` --- if the two leading syllables agree then
  `|x⁻¹y| + 2|u|ᵢ ≤ |x| + |y|`: at least the leading syllable cancels.

The first of the three carries the content, and it is `wordNorm_inv_mul_of_fstIdx_ne`:
an induction on the number of syllables of `p` which never looks at the *back*
of a word.  Peeling the leading syllable `⟨i,a⟩` off `p` turns `p⁻¹ * m` into
`p''⁻¹ * (of a⁻¹ * m)`, and `of a⁻¹ * m` is again a word whose leading syllable
lies in the factor `i` that `p''` avoids.  So the seam stays at the front, where
Mathlib's `Monoid.CoprodI.Word` API lives, and no concatenation of reduced words
ever has to be built.

The other two are corollaries: `wordNorm_branch_same` applies the first to `x'`
and `of (u⁻¹v) * y'`, and `wordNorm_same_lead` is subadditivity after the two
leading syllables have cancelled.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm

/-- **Subadditivity across an inverse**: `|x⁻¹z| ≤ |x| + |z|`.  This is the only
bound available when neither branch lemma applies, and it is what the easy
branches of the four-point case analysis use. -/
theorem wordNorm_inv_mul_le {H : Type*} [Group H] {C : Set H}
    (hC : IsSymmetricGeneratingSet C) (x z : H) :
    wordNorm C (x⁻¹ * z) ≤ wordNorm C x + wordNorm C z := by
  have h := wordNorm_mul_le hC x⁻¹ z
  rwa [wordNorm_inv hC] at h

section NormalForm

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-! ## The leading syllable -/

/-- **The leading syllable of the normal form of `g`**, as an option: `none`
exactly when `g = 1`.  The whole four-point case analysis is a case analysis on
the three leading syllables of `x`, `y`, `z`. -/
def lead (g : CoprodI G) : Option (Σ i, G i) := (Word.equiv g).toList.head?

theorem lead_eq_none_iff {g : CoprodI G} : lead g = none ↔ g = 1 := by
  constructor
  · intro h
    refine sylLength_eq_zero_iff.mp ?_
    rcases hl : (Word.equiv g).toList with _ | ⟨a, l⟩
    · simp [sylLength, hl]
    · unfold lead at h
      rw [hl] at h
      simp at h
  · rintro rfl
    show ((Word.equiv (1 : CoprodI G)).toList).head? = none
    rw [equiv_one]; rfl

/-- The first index of the normal form, read off the leading syllable. -/
theorem fstIdx_of_lead_some {g : CoprodI G} {i : ι} {u : G i}
    (h : lead g = some ⟨i, u⟩) : Word.fstIdx (Word.equiv g) = some i := by
  unfold lead at h
  simp [Word.fstIdx, h]

/-- Equal leading syllables give equal first indices. -/
theorem fstIdx_congr {x y : CoprodI G} (h : lead x = lead y) :
    Word.fstIdx (Word.equiv x) = Word.fstIdx (Word.equiv y) := by
  show (lead x).map Sigma.fst = (lead y).map Sigma.fst
  rw [h]

/-- **Reading the leading letter at a known index.**  This is what lets the
four-point case analysis branch on `Word.fstIdx (Word.equiv y) = some i` --- a
statement about the *index* alone --- and still produce a letter of `G i`, so
that no equality between two index variables ever has to be substituted. -/
theorem exists_lead_index {g : CoprodI G} {i : ι}
    (h : Word.fstIdx (Word.equiv g) = some i) : ∃ v : G i, lead g = some ⟨i, v⟩ := by
  have h2 : (Word.equiv g).toList.head?.map Sigma.fst = some i := h
  rcases hl : (Word.equiv g).toList with _ | ⟨a, l⟩
  · rw [hl] at h2
    simp at h2
  · obtain ⟨j, v⟩ := a
    have hj : j = i := by
      rw [hl] at h2
      simpa using h2
    subst hj
    exact ⟨v, by unfold lead; rw [hl]; rfl⟩

/-! ## Prepending a syllable -/

/-- **Prepending a letter of a factor the word avoids.**  If the normal form of
`g` does not begin in the factor `i` and `z : G i` is nontrivial, the normal
form of `of z * g` is that of `g` with `⟨i,z⟩` in front: nothing reduces. -/
theorem toList_equiv_of_mul {i : ι} {z : G i} (hz : z ≠ 1) {g : CoprodI G}
    (hg : Word.fstIdx (Word.equiv g) ≠ some i) :
    (Word.equiv (CoprodI.of z * g)).toList = ⟨i, z⟩ :: (Word.equiv g).toList := by
  have hw : (Word.cons z (Word.equiv g) hg hz).prod = CoprodI.of z * g := by
    rw [Word.prod_cons, prod_equiv]
  have hkey := equiv_prod (Word.cons z (Word.equiv g) hg hz)
  rw [hw] at hkey
  exact congrArg Word.toList hkey

/-- The same, as a word length: prepending a syllable costs exactly that
syllable's factor length. -/
theorem wordNorm_of_mul (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {i : ι}
    {z : G i} (hz : z ≠ 1) {g : CoprodI G}
    (hg : Word.fstIdx (Word.equiv g) ≠ some i) :
    wordNorm (unionCarrier S) (CoprodI.of z * g)
      = wordNorm (S i) z + wordNorm (unionCarrier S) g := by
  rw [wordNorm_eq_syllableNorm hS, wordNorm_eq_syllableNorm hS]
  show wsum S (Word.equiv (CoprodI.of z * g))
    = wordNorm (S i) z + wsum S (Word.equiv g)
  simp only [wsum, toList_equiv_of_mul hz hg, List.map_cons, List.sum_cons]

/-- The first index of a word with a syllable prepended. -/
theorem fstIdx_of_mul {i : ι} {z : G i} (hz : z ≠ 1) {g : CoprodI G}
    (hg : Word.fstIdx (Word.equiv g) ≠ some i) :
    Word.fstIdx (Word.equiv (CoprodI.of z * g)) = some i := by
  simp [Word.fstIdx, toList_equiv_of_mul hz hg]

/-! ## Splitting off the leading syllable -/

/-- **The normal form of `g`, split at its leading syllable.**  Every piece the
induction below needs: the tail `g'`, that the leading letter is nontrivial,
that the tail avoids the leading factor, that the tail is one syllable shorter,
and that the length splits. -/
theorem exists_split (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {g : CoprodI G}
    {i : ι} {u : G i} (h : lead g = some ⟨i, u⟩) :
    ∃ g' : CoprodI G, g = CoprodI.of u * g' ∧ u ≠ 1 ∧
      Word.fstIdx (Word.equiv g') ≠ some i ∧
      (Word.equiv g).toList.length = (Word.equiv g').toList.length + 1 ∧
      wordNorm (unionCarrier S) g
        = wordNorm (S i) u + wordNorm (unionCarrier S) g' := by
  unfold lead at h
  obtain ⟨l, hl⟩ : ∃ l, (Word.equiv g).toList = ⟨i, u⟩ :: l :=
    exists_cons_of_head?_eq h
  have hu : u ≠ 1 := (Word.equiv g).ne_one ⟨i, u⟩ (by rw [hl]; simp)
  have hg' : (Word.equiv (CoprodI.of u⁻¹ * g)).toList = l := by
    rw [equiv_of_mul, toList_of_smul u⁻¹ hl, if_pos (inv_mul_cancel u)]
  have hgeq : (CoprodI.of u : CoprodI G) * (CoprodI.of u⁻¹ * g) = g := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have htail : (Word.equivPair i (Word.equiv g)).tail.toList = l :=
    (equivPair_head_of_cons hl).2
  have hword : Word.equiv (CoprodI.of u⁻¹ * g)
      = (Word.equivPair i (Word.equiv g)).tail := Word.ext (by rw [hg', htail])
  have hidx : Word.fstIdx (Word.equiv (CoprodI.of u⁻¹ * g)) ≠ some i := by
    rw [hword]
    exact (Word.equivPair i (Word.equiv g)).fstIdx_ne
  refine ⟨CoprodI.of u⁻¹ * g, hgeq.symm, hu, hidx, ?_, ?_⟩
  · rw [hl, hg', List.length_cons]
  · have hnorm := wordNorm_of_mul hS hu hidx
    rwa [hgeq] at hnorm

/-! ## No cancellation between two words that branch immediately -/

/-- **The branch formula, by induction on the leading word.**
`|p⁻¹m| = |p| + |m|` as soon as the two normal forms begin in different
factors --- including the case where one of them is empty.

The induction peels the leading syllable `⟨i,a⟩` off `p`.  Multiplying it into
`m` on the left is a *prepend*, because `m` does not begin in the factor `i`;
the resulting word `of a⁻¹ * m` begins in `i`, which is exactly the factor the
remaining `p''` avoids, so the inductive hypothesis applies to the shorter pair
`(p'', of a⁻¹ * m)`, and `p''⁻¹ * (of a⁻¹ * m) = p⁻¹ * m`. -/
theorem wordNorm_inv_mul_of_fstIdx_ne (hS : ∀ i, IsSymmetricGeneratingSet (S i)) :
    ∀ (n : ℕ) (p m : CoprodI G), (Word.equiv p).toList.length ≤ n →
      Word.fstIdx (Word.equiv p) ≠ Word.fstIdx (Word.equiv m) →
        wordNorm (unionCarrier S) (p⁻¹ * m)
          = wordNorm (unionCarrier S) p + wordNorm (unionCarrier S) m := by
  intro n
  induction n with
  | zero =>
      intro p m hlen _
      have hp : p = 1 := by
        refine sylLength_eq_zero_iff.mp ?_
        have : (Word.equiv p).toList.length = 0 := Nat.le_zero.mp hlen
        simpa [sylLength] using this
      rw [hp, inv_one, one_mul, wordNorm_one, Nat.zero_add]
  | succ n ih =>
      intro p m hlen hne
      rcases hl : lead p with _ | ⟨i, u⟩
      · have hp : p = 1 := lead_eq_none_iff.mp hl
        rw [hp, inv_one, one_mul, wordNorm_one, Nat.zero_add]
      · obtain ⟨p', hpeq, hu, hp'idx, hp'len, hp'norm⟩ := exists_split hS hl
        have hfstp : Word.fstIdx (Word.equiv p) = some i := fstIdx_of_lead_some hl
        have hm : Word.fstIdx (Word.equiv m) ≠ some i := by
          intro hcon
          exact hne (by rw [hfstp, hcon])
        have huinv : (u⁻¹ : G i) ≠ 1 := inv_ne_one.mpr hu
        have hm'fst : Word.fstIdx (Word.equiv (CoprodI.of u⁻¹ * m)) = some i :=
          fstIdx_of_mul huinv hm
        have hm'norm : wordNorm (unionCarrier S) (CoprodI.of u⁻¹ * m)
            = wordNorm (S i) u + wordNorm (unionCarrier S) m := by
          rw [wordNorm_of_mul hS huinv hm, wordNorm_inv (hS i)]
        have hstep := ih p' (CoprodI.of u⁻¹ * m) (by omega)
          (by rw [hm'fst]; exact hp'idx)
        have hinv : (CoprodI.of u : CoprodI G)⁻¹ = CoprodI.of u⁻¹ :=
          (map_inv (CoprodI.of : G i →* CoprodI G) u).symm
        have hprod : p'⁻¹ * (CoprodI.of u⁻¹ * m) = p⁻¹ * m := by
          have hpi : (p : CoprodI G)⁻¹ = p'⁻¹ * CoprodI.of u⁻¹ := by
            rw [hpeq, mul_inv_rev, hinv]
          rw [hpi, mul_assoc]
        rw [← hprod, hstep, hm'norm, hp'norm]
        omega

/-! ## The three shapes the four-point condition uses -/

/-- **Nothing cancels between two words that begin in different factors.** -/
theorem wordNorm_branch (hS : ∀ i, IsSymmetricGeneratingSet (S i))
    {x y : CoprodI G}
    (h : Word.fstIdx (Word.equiv x) ≠ Word.fstIdx (Word.equiv y)) :
    wordNorm (unionCarrier S) (x⁻¹ * y)
      = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) y :=
  wordNorm_inv_mul_of_fstIdx_ne hS (Word.equiv x).toList.length x y le_rfl h

/-- **Exactly the two leading syllables merge.**  If `x` and `y` begin in the
same factor with *different* leading letters `u ≠ v`, the normal form of `x⁻¹y`
is the reverse of the tail of `x`, then the single syllable `u⁻¹v`, then the
tail of `y`, and the length is the sum of the three. -/
theorem wordNorm_branch_same (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {i : ι}
    {u v : G i} {x y : CoprodI G} (hx : lead x = some ⟨i, u⟩)
    (hy : lead y = some ⟨i, v⟩) (huv : u ≠ v) :
    wordNorm (unionCarrier S) (x⁻¹ * y) + wordNorm (S i) u + wordNorm (S i) v
      = wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) y
        + wordNorm (S i) (u⁻¹ * v) := by
  obtain ⟨x', hxeq, -, hx'idx, -, hxnorm⟩ := exists_split hS hx
  obtain ⟨y', hyeq, -, hy'idx, -, hynorm⟩ := exists_split hS hy
  have huv1 : (u⁻¹ * v : G i) ≠ 1 := fun h => huv (inv_mul_eq_one.mp h)
  have hmfst : Word.fstIdx (Word.equiv (CoprodI.of (u⁻¹ * v) * y')) = some i :=
    fstIdx_of_mul huv1 hy'idx
  have hmnorm : wordNorm (unionCarrier S) (CoprodI.of (u⁻¹ * v) * y')
      = wordNorm (S i) (u⁻¹ * v) + wordNorm (unionCarrier S) y' :=
    wordNorm_of_mul hS huv1 hy'idx
  have hstep : wordNorm (unionCarrier S) (x'⁻¹ * (CoprodI.of (u⁻¹ * v) * y'))
      = wordNorm (unionCarrier S) x'
        + wordNorm (unionCarrier S) (CoprodI.of (u⁻¹ * v) * y') :=
    wordNorm_branch hS (by rw [hmfst]; exact hx'idx)
  have hinv : (CoprodI.of u : CoprodI G)⁻¹ = CoprodI.of u⁻¹ :=
    (map_inv (CoprodI.of : G i →* CoprodI G) u).symm
  have hsplit : (CoprodI.of (u⁻¹ * v) : CoprodI G)
      = CoprodI.of u⁻¹ * CoprodI.of v := map_mul _ _ _
  have hprod : x'⁻¹ * (CoprodI.of (u⁻¹ * v) * y') = x⁻¹ * y := by
    rw [hsplit, hxeq, hyeq, mul_inv_rev, hinv]
    simp only [mul_assoc]
  rw [← hprod, hstep, hmnorm, hxnorm, hynorm]
  omega

/-- **At least the leading syllable cancels.**  If `x` and `z` have the same
leading syllable, the two copies of it disappear from `x⁻¹z`. -/
theorem wordNorm_same_lead (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {i : ι}
    {u : G i} {x z : CoprodI G} (hx : lead x = some ⟨i, u⟩)
    (hz : lead z = some ⟨i, u⟩) :
    wordNorm (unionCarrier S) (x⁻¹ * z) + 2 * wordNorm (S i) u
      ≤ wordNorm (unionCarrier S) x + wordNorm (unionCarrier S) z := by
  obtain ⟨x', hxeq, -, -, -, hxnorm⟩ := exists_split hS hx
  obtain ⟨z', hzeq, -, -, -, hznorm⟩ := exists_split hS hz
  have hprod : x⁻¹ * z = x'⁻¹ * z' := by
    rw [hxeq, hzeq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hsub := wordNorm_inv_mul_le (isSymmetricGeneratingSet_unionCarrier hS) x' z'
  rw [hprod, hxnorm, hznorm]
  omega

end NormalForm

end HullSCUnionGeometry
end GroupApproximation
