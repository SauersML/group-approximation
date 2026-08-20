import GroupApproximation.Algebra.FreeProductCyclicWord

/-!
# Length, powers and conjugacy in a free product

`Algebra.FreeProductCyclicWord` reduced every element to a conjugate of a
syllable or of a cyclically reduced word.  This file proves the two facts that
make that reduction *sharp*, and both are unconditional:

* **a cyclically reduced word is shortest in its conjugacy class**
  (`length_le_sylLength_conj`), and
* **a cyclically reduced word of two or more syllables is not conjugate into a
  factor** (`not_conj_of_le_one`),

so the trichotomy of `exists_cyclicReduction` is a genuine classification: the
cases exclude one another, and the syllable length of the cyclically reduced
form is a conjugacy invariant.

## The mechanism: powers, not normal forms

The classical proofs of both statements go through the *palindromic
conjugation normal form* — write `c u c⁻¹` as a reduced word `d · (rotation
of u) · d⁻¹` — which over a free product is delicate, because conjugating by
part of a syllable rotates the word to a *split* syllable and the "rotation"
has to be defined up to that.

None of that is needed.  Both statements follow from two length facts:

* `sylLength_mul_le` — syllable length is subadditive.  Peel the head letter
  and induct; the whole content is that multiplying by one letter adds at most
  one syllable.
* `sylLength_npow` — for a *cyclically reduced* `u`, `|uⁿ| = n·|u|` **on the
  nose**, because `NeWord.append` spells `uⁿ` as a reduced word.

Together: if `g` is conjugate to `u` by `c`, then `uⁿ = c⁻¹ gⁿ c` gives
`n·|u| ≤ n·|g| + 2·|c|` for *every* `n`, and one `n` past `2·|c|` forces
`|u| ≤ |g|`.  The same comparison against a syllable — whose powers stay one
syllable long, so `|c xⁿ c⁻¹|` is *bounded* — rules out conjugacy into a
factor outright.

This is the stable-length argument, and it replaces a normal-form analysis by
two inductions on `ℕ`.
-/

namespace GroupApproximation
namespace FreeProductCyclic

open Monoid Monoid.CoprodI

section Length

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-! ### Subadditivity -/

/-- **The head letter, split off as a factor.**  Every nonidentity element is
one letter times something one syllable shorter. -/
theorem exists_head_factor {g : CoprodI G} (hg : g ≠ 1) :
    ∃ (i : ι) (x : G i) (g' : CoprodI G),
      g = CoprodI.of x * g' ∧ sylLength g' + 1 = sylLength g := by
  obtain ⟨p, q, u, hu, hup⟩ := exists_neWord hg
  have hhead : (Word.equiv g).toList.head? = some ⟨p, u.head⟩ := by
    rw [← hu]; exact NeWord.toList_head? u
  obtain ⟨l, hl⟩ := exists_cons_of_head?_eq hhead
  refine ⟨p, u.head, CoprodI.of (u.head)⁻¹ * g, ?_, ?_⟩
  · rw [map_inv]
    group
  · rw [sylLength_of_smul_cancel hl]
    simp only [sylLength, hl, List.length_cons]

private theorem sylLength_mul_le_aux :
    ∀ (n : ℕ) (a b : CoprodI G), sylLength a ≤ n →
      sylLength (a * b) ≤ sylLength a + sylLength b := by
  intro n
  induction n with
  | zero =>
      intro a b ha
      have h1 : a = 1 := sylLength_eq_zero_iff.mp (Nat.le_zero.mp ha)
      subst h1
      simp [sylLength]
  | succ n ih =>
      intro a b ha
      by_cases h1 : a = 1
      · subst h1
        simp [sylLength]
      · obtain ⟨i, x, a', hax, hlen⟩ := exists_head_factor h1
        have ha' : sylLength a' ≤ n := by omega
        have hstep : sylLength (CoprodI.of x * (a' * b)) ≤ sylLength (a' * b) + 1 :=
          sylLength_of_mul_le x (a' * b)
        have hih := ih a' b ha'
        rw [hax] at hlen
        rw [hax, mul_assoc]
        omega

/-- **Syllable length is subadditive.** -/
theorem sylLength_mul_le (a b : CoprodI G) :
    sylLength (a * b) ≤ sylLength a + sylLength b :=
  sylLength_mul_le_aux (sylLength a) a b le_rfl

theorem sylLength_pow_le (a : CoprodI G) :
    ∀ n : ℕ, sylLength (a ^ n) ≤ n * sylLength a
  | 0 => by simp [sylLength]
  | (n + 1) => by
      have h1 : sylLength (a ^ n * a) ≤ sylLength (a ^ n) + sylLength a :=
        sylLength_mul_le _ _
      have h2 := sylLength_pow_le a n
      rw [pow_succ]
      have h3 : n * sylLength a + sylLength a = (n + 1) * sylLength a := by ring
      omega

/-- Conjugation moves syllable length by at most twice the conjugator. -/
theorem sylLength_conj_le (c g : CoprodI G) :
    sylLength (c * g * c⁻¹) ≤ 2 * sylLength c + sylLength g := by
  have h1 : sylLength (c * g * c⁻¹) ≤ sylLength (c * g) + sylLength c⁻¹ :=
    sylLength_mul_le _ _
  have h2 : sylLength (c * g) ≤ sylLength c + sylLength g := sylLength_mul_le _ _
  have h3 : sylLength c⁻¹ = sylLength c := sylLength_inv c
  omega

/-! ### Powers of a cyclically reduced word -/

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem npow_toList_length {i j : ι} (hij : i ≠ j) (u : NeWord G i j) :
    ∀ n : ℕ, (npow hij u n).toList.length = (n + 1) * u.toList.length
  | 0 => by simp [npow]
  | (n + 1) => by
      have hih := npow_toList_length hij u n
      rw [npow]
      simp only [NeWord.toList, List.length_append, hih]
      ring

/-- **Powers of a cyclically reduced word have exactly proportional length.**
No cancellation is possible: `NeWord.append` spells `uⁿ` as a reduced word. -/
theorem sylLength_npow {i j : ι} (hij : i ≠ j) (u : NeWord G i j) (n : ℕ) :
    sylLength (u.prod ^ (n + 1)) = (n + 1) * u.toList.length := by
  have h1 : (npow hij u n).toWord = Word.equiv (u.prod ^ (n + 1)) := by
    rw [← npow_prod hij u n]
    exact (equiv_prod _).symm
  rw [sylLength_eq_of_neWord h1, npow_toList_length hij u n]

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
/-- A cyclically reduced word has at least two syllables: a one-letter word
begins and ends in the same factor. -/
theorem two_le_length_of_ne {i j : ι} (hij : i ≠ j) (u : NeWord G i j) :
    2 ≤ u.toList.length := by
  cases u with
  | singleton x hx => exact absurd rfl hij
  | append u₁ hne u₂ =>
      have h1 : u₁.toList ≠ [] := NeWord.toList_ne_nil u₁
      have h2 : u₂.toList ≠ [] := NeWord.toList_ne_nil u₂
      have hp1 : 1 ≤ u₁.toList.length := by
        cases hc : u₁.toList with
        | nil => exact absurd hc h1
        | cons a t => simp
      have hp2 : 1 ≤ u₂.toList.length := by
        cases hc : u₂.toList with
        | nil => exact absurd hc h2
        | cons a t => simp
      simp only [NeWord.toList, List.length_append]
      omega

/-! ### The two sharpness statements -/

/-- **A cyclically reduced word is shortest in its conjugacy class.**

For every `n`, `uⁿ = c⁻¹ gⁿ c` bounds `n·|u|` by `n·|g| + 2·|c|`; one `n`
past `2·|c|` forces `|u| ≤ |g|`. -/
theorem length_le_sylLength_conj {i j : ι} (hij : i ≠ j) (u : NeWord G i j)
    (c : CoprodI G) :
    u.toList.length ≤ sylLength (c * u.prod * c⁻¹) := by
  by_contra hlt
  push Not at hlt
  have key : ∀ n : ℕ,
      (n + 1) * u.toList.length
        ≤ (n + 1) * sylLength (c * u.prod * c⁻¹) + 2 * sylLength c := by
    intro n
    have h1 : sylLength (u.prod ^ (n + 1)) = (n + 1) * u.toList.length :=
      sylLength_npow hij u n
    have h2 : u.prod ^ (n + 1) = c⁻¹ * (c * u.prod * c⁻¹) ^ (n + 1) * c := by
      rw [conj_pow_eq]
      group
    have h3 : sylLength (c⁻¹ * (c * u.prod * c⁻¹) ^ (n + 1) * c)
        ≤ 2 * sylLength c⁻¹ + sylLength ((c * u.prod * c⁻¹) ^ (n + 1)) := by
      have h := sylLength_conj_le c⁻¹ ((c * u.prod * c⁻¹) ^ (n + 1))
      rw [inv_inv] at h
      exact h
    have h4 : sylLength ((c * u.prod * c⁻¹) ^ (n + 1))
        ≤ (n + 1) * sylLength (c * u.prod * c⁻¹) :=
      sylLength_pow_le _ (n + 1)
    have h5 : sylLength c⁻¹ = sylLength c := sylLength_inv c
    rw [h2] at h1
    omega
  have hkey := key (2 * sylLength c)
  have hmul : (2 * sylLength c + 1) * (sylLength (c * u.prod * c⁻¹) + 1)
      ≤ (2 * sylLength c + 1) * u.toList.length :=
    Nat.mul_le_mul (le_refl _) hlt
  rw [Nat.mul_add, mul_one] at hmul
  omega

/-- **A cyclically reduced word of two or more syllables is not conjugate into
a factor.**  Powers of a syllable stay one syllable long, so their conjugates
have *bounded* length, while `|uⁿ| = n·|u|` grows. -/
theorem not_conj_of_le_one {i j : ι} (hij : i ≠ j) (u : NeWord G i j)
    {k : ι} (x : G k) (c : CoprodI G) :
    u.prod ≠ c * CoprodI.of x * c⁻¹ := by
  intro heq
  have hL2 : 2 ≤ u.toList.length := two_le_length_of_ne hij u
  have key : ∀ n : ℕ, (n + 1) * u.toList.length ≤ 2 * sylLength c + 1 := by
    intro n
    have h1 : sylLength (u.prod ^ (n + 1)) = (n + 1) * u.toList.length :=
      sylLength_npow hij u n
    have h2 : u.prod ^ (n + 1) = c * CoprodI.of (x ^ (n + 1)) * c⁻¹ := by
      rw [heq, conj_pow_eq, map_pow]
    have h3 : sylLength (c * CoprodI.of (x ^ (n + 1)) * c⁻¹)
        ≤ 2 * sylLength c + sylLength (CoprodI.of (x ^ (n + 1))) :=
      sylLength_conj_le c _
    have h4 : sylLength (CoprodI.of (x ^ (n + 1))) ≤ 1 := sylLength_of_le_one _
    rw [h2] at h1
    omega
  have h := key (2 * sylLength c + 1)
  have h' : (2 * sylLength c + 1 + 1) * 2
      ≤ (2 * sylLength c + 1 + 1) * u.toList.length :=
    Nat.mul_le_mul (le_refl _) hL2
  omega

/-- **The syllable length of a cyclically reduced form is a conjugacy
invariant.** -/
theorem length_eq_of_conj {i j i' j' : ι} (hij : i ≠ j) (hij' : i' ≠ j')
    (u : NeWord G i j) (v : NeWord G i' j') (c : CoprodI G)
    (h : v.prod = c * u.prod * c⁻¹) :
    u.toList.length = v.toList.length := by
  have h1 : u.toList.length ≤ v.toList.length := by
    have := length_le_sylLength_conj hij u c
    rw [← h] at this
    have h2 : sylLength v.prod = v.toList.length := by
      apply sylLength_eq_of_neWord
      exact (equiv_prod _).symm
    omega
  have h2 : v.toList.length ≤ u.toList.length := by
    have hback : u.prod = c⁻¹ * v.prod * c := by
      rw [h]; group
    have := length_le_sylLength_conj hij' v c⁻¹
    rw [inv_inv] at this
    rw [← hback] at this
    have h3 : sylLength u.prod = u.toList.length := by
      apply sylLength_eq_of_neWord
      exact (equiv_prod _).symm
    omega
  omega

/-- **The torsion classification of a free product, as an equivalence.**  The
forward direction is `torsion_conj_into_factor`; the converse is immediate,
and together they say that the torsion of a free product is exactly the
torsion of its factors, spread over conjugates. -/
theorem isOfFinOrder_iff_conj_factor [Nonempty ι] {g : CoprodI G} :
    IsOfFinOrder g ↔ ∃ (i : ι) (x : G i) (c : CoprodI G),
      IsOfFinOrder x ∧ g = c * CoprodI.of x * c⁻¹ := by
  constructor
  · intro hfin
    obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    rcases torsion_conj_into_factor hn hgn with h | ⟨i, x, c, hx, hgc⟩
    · refine ⟨Classical.arbitrary ι, 1, 1,
        isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, by simp⟩, ?_⟩
      simp [h]
    · exact ⟨i, x, c, isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hx⟩, hgc⟩
  · rintro ⟨i, x, c, hx, rfl⟩
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
    rw [conj_pow_eq, ← map_pow, hxn, map_one, mul_one, mul_inv_cancel]

end Length

end FreeProductCyclic
end GroupApproximation
