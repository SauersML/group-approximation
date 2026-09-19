import Mathlib.Tactic.Group
import GroupApproximation.Algebra.FreeProductOrder
import GroupApproximation.Algebra.GroupTorsionFree

/-!
# Cyclic reduction in a free product, and where torsion can live

`Algebra.FreeProductOrder` proved that *one* explicitly written alternating
word is nontrivial.  This file proves the general statement behind it: every
element of a free product is conjugate to one that is either a single syllable
or genuinely cyclically reduced, and the second kind has infinite order.  The
consequence is the classical

> **torsion in a free product is conjugate into a factor**

and, as a corollary, that a free product of torsion-free groups is
torsion-free.  Neither is in Mathlib, which supplies the normal form
(`Monoid.CoprodI.Word.equiv`) and the ping-pong lemma and stops there.

## Why this file exists

It is the base case of Osin's theorem, in the sense of
`Sofic.OsinRelativeSmallCancellation`.  A small-cancellation quotient of
`U * H` is asked to keep `U` embedded and to stay torsion-free; for the empty
relator family the quotient *is* `U * H`, so the two clauses become "`U`
embeds in `U * H`" (Mathlib's `Monoid.CoprodI.of_injective`) and "`U * H` is
torsion-free" — which is this file.  Every relative statement downstream
degenerates to these, so nothing there can be vacuous.

## The mechanism, and the one place it is delicate

Everything is measured by `sylLength`, the number of letters in the normal
form.  Mathlib's word API is *head-oriented*: `Word.equivPair` splits off the
first letter and the `MulAction` multiplies on the left, so peeling a letter
off the front (`sylLength_of_smul_cancel`) is a two-line computation, while
peeling one off the back is not available at all.

The back is reached through `NeWord.inv`, whose `head` Mathlib already
identifies with the original `last` (`NeWord.inv_head`).  Since
`g * (of y)⁻¹ = (of y * g⁻¹)⁻¹` and inversion preserves syllable length
(`sylLength_inv`), the front-peeling lemma peels the back as well
(`sylLength_mul_inv_last`).  That is the only trick in the file, and it is
what makes the cyclic-reduction induction one page rather than a development.

The induction itself is on `sylLength`.  A word of length at least two whose
first and last letters lie in the *same* factor is conjugated by its last
letter: the front letter absorbs it and the back letter is peeled, so the
length drops.  A word whose first and last letters lie in *different* factors
is already cyclically reduced, and `npow` spells its powers as reduced words,
so it has infinite order.
-/

namespace GroupApproximation
namespace FreeProductCyclic

open Monoid Monoid.CoprodI

section Words

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)]

/-- **Syllable length**: the number of letters in the normal form. -/
def sylLength (g : CoprodI G) : ℕ := (Word.equiv g).toList.length

/-! ### The normal form, unpacked

`Word.equiv` is an `Equiv` whose inverse *is* `Word.prod`, definitionally.
The three lemmas below are that fact in the three shapes the file uses. -/

theorem equiv_symm_eq_prod (w : Word G) : Word.equiv.symm w = w.prod := rfl

theorem prod_equiv (g : CoprodI G) : (Word.equiv g).prod = g :=
  Word.equiv.symm_apply_apply g

theorem equiv_prod (w : Word G) : Word.equiv w.prod = w :=
  Word.equiv.apply_symm_apply w

@[simp] theorem equiv_one : Word.equiv (1 : CoprodI G) = Word.empty := by
  -- the empty word's product is `1`, and `equiv` inverts `prod`
  simpa using equiv_prod (G := G) Word.empty

theorem sylLength_eq_zero_iff {g : CoprodI G} : sylLength g = 0 ↔ g = 1 := by
  constructor
  · intro h
    have hnil : (Word.equiv g).toList = [] := by
      rcases hl : (Word.equiv g).toList with _ | ⟨a, l⟩
      · rfl
      · simp only [sylLength, hl, List.length_cons] at h
        omega
    have hw : Word.equiv g = Word.empty := Word.ext hnil
    have hp := prod_equiv g
    rw [hw, Word.prod_empty] at hp
    exact hp.symm
  · rintro rfl
    simp [sylLength]

/-- A list whose first entry is known is a `cons`.  Stated at a list variable
so that the `cases` inside is a substitution and nothing in the caller's goal
is generalized. -/
theorem exists_cons_of_head?_eq {α : Type*} {l : List α} {a : α}
    (h : l.head? = some a) : ∃ t, l = a :: t := by
  cases l with
  | nil => simp at h
  | cons b t =>
      refine ⟨t, ?_⟩
      simp only [List.head?_cons, Option.some.injEq] at h
      rw [h]

/-! ### Left multiplication by one letter

`Word.rcons` is the only constructor that can shorten a word, and it shortens
it exactly when the new head cancels. -/

theorem rcons_equivPair (i : ι) (w : Word G) :
    Word.rcons (Word.equivPair i w) = w :=
  (Word.equivPair i).symm_apply_apply w

omit [DecidableEq ι] in
theorem toList_rcons {i : ι} (p : Word.Pair G i) :
    (Word.rcons p).toList =
      if p.head = 1 then p.tail.toList else ⟨i, p.head⟩ :: p.tail.toList := by
  unfold Word.rcons
  by_cases h : p.head = 1
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]
    rfl

omit [DecidableEq ι] in
theorem length_rcons {i : ι} (p : Word.Pair G i) :
    (Word.rcons p).toList.length =
      if p.head = 1 then p.tail.toList.length else p.tail.toList.length + 1 := by
  rw [toList_rcons]
  by_cases h : p.head = 1 <;> simp [h]

theorem length_tail_equivPair_le (i : ι) (w : Word G) :
    (Word.equivPair i w).tail.toList.length ≤ w.toList.length := by
  conv_rhs => rw [← rcons_equivPair i w]
  rw [length_rcons]
  split_ifs <;> omega

/-- **The head letter, read off the pair decomposition.**  A word beginning
with `⟨i, x⟩` splits at `i` as `x` followed by the rest: the head cannot be
trivial, because then the tail would begin at `i` again, which the pair
forbids. -/
theorem equivPair_head_of_cons {i : ι} {x : G i} {l : List (Σ i, G i)}
    {w : Word G} (hw : w.toList = ⟨i, x⟩ :: l) :
    (Word.equivPair i w).head = x ∧ (Word.equivPair i w).tail.toList = l := by
  have hrc : (Word.rcons (Word.equivPair i w)).toList = ⟨i, x⟩ :: l := by
    rw [rcons_equivPair]; exact hw
  rw [toList_rcons] at hrc
  by_cases hh : (Word.equivPair i w).head = 1
  · exfalso
    rw [if_pos hh] at hrc
    have hfst : Word.fstIdx (Word.equivPair i w).tail = some i := by
      simp [Word.fstIdx, hrc]
    exact (Word.equivPair i w).fstIdx_ne hfst
  · rw [if_neg hh] at hrc
    injection hrc with h1 h2
    exact ⟨by simpa using h1, h2⟩

theorem equiv_of_mul {i : ι} (x : G i) (g : CoprodI G) :
    Word.equiv (CoprodI.of x * g) = CoprodI.of x • Word.equiv g := by
  show (CoprodI.of x * g) • (Word.empty : Word G)
      = CoprodI.of x • (g • (Word.empty : Word G))
  rw [mul_smul]

/-- **Multiplying a word by a letter of the same factor**, computed. -/
theorem toList_of_smul {i : ι} (z : G i) {x : G i} {l : List (Σ i, G i)}
    {w : Word G} (hw : w.toList = ⟨i, x⟩ :: l) :
    (CoprodI.of z • w).toList = if z * x = 1 then l else ⟨i, z * x⟩ :: l := by
  obtain ⟨hh, ht⟩ := equivPair_head_of_cons hw
  have hrc : (CoprodI.of z • w).toList
      = (Word.rcons (Word.equivPair i (CoprodI.of z • w))).toList := by
    rw [rcons_equivPair]
  rw [hrc, toList_rcons, Word.equivPair_smul_same]
  simp [hh, ht]

/-- Left multiplication by a letter can add at most one syllable. -/
theorem sylLength_of_mul_le {i : ι} (z : G i) (g : CoprodI G) :
    sylLength (CoprodI.of z * g) ≤ sylLength g + 1 := by
  have hle := length_tail_equivPair_le i (Word.equiv g)
  simp only [sylLength, equiv_of_mul, Word.of_smul_def, length_rcons]
  split_ifs <;> omega

/-- A single letter is a word of length at most one. -/
theorem sylLength_of_le_one {i : ι} (z : G i) :
    sylLength (CoprodI.of z) ≤ 1 := by
  have h := sylLength_of_mul_le z (1 : CoprodI G)
  rw [mul_one] at h
  have h1 : sylLength (1 : CoprodI G) = 0 := sylLength_eq_zero_iff.mpr rfl
  omega

/-- **Peeling the front letter.**  Multiplying by the inverse of the first
letter deletes it. -/
theorem sylLength_of_smul_cancel {i : ι} {x : G i} {l : List (Σ i, G i)}
    {g : CoprodI G} (hg : (Word.equiv g).toList = ⟨i, x⟩ :: l) :
    sylLength (CoprodI.of x⁻¹ * g) = l.length := by
  have h2 : (CoprodI.of x⁻¹ • Word.equiv g).toList
      = if x⁻¹ * x = 1 then l else (⟨i, x⁻¹ * x⟩ : Σ i, G i) :: l :=
    toList_of_smul _ hg
  rw [if_pos (inv_mul_cancel x)] at h2
  simp only [sylLength, equiv_of_mul, h2]

/-- Left multiplication by a letter of the leading factor never lengthens. -/
theorem sylLength_of_smul_le {i : ι} (z : G i) {x : G i} {l : List (Σ i, G i)}
    {g : CoprodI G} (hg : (Word.equiv g).toList = ⟨i, x⟩ :: l) :
    sylLength (CoprodI.of z * g) ≤ sylLength g := by
  have hlen : sylLength g = l.length + 1 := by
    simp only [sylLength, hg, List.length_cons]
  have h2 : sylLength (CoprodI.of z * g)
      = (if z * x = 1 then l else (⟨i, z * x⟩ : Σ i, G i) :: l).length := by
    simp only [sylLength, equiv_of_mul, toList_of_smul z hg]
  rw [h2, hlen]
  split_ifs with h
  · exact Nat.le_succ _
  · exact le_of_eq List.length_cons

private theorem getLast?_cons_of_ne_nil {α : Type*} (a : α) {l : List α}
    (hl : l ≠ []) : (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b t => rfl

/-- **The back letter is untouched by multiplication at the front**, as soon
as there is more than one letter to begin with. -/
theorem getLast?_of_smul {i : ι} (z : G i) {x : G i} {l : List (Σ i, G i)}
    {g : CoprodI G} (hg : (Word.equiv g).toList = ⟨i, x⟩ :: l) (hl : l ≠ []) :
    (Word.equiv (CoprodI.of z * g)).toList.getLast?
      = (Word.equiv g).toList.getLast? := by
  rw [equiv_of_mul, toList_of_smul z hg, hg]
  by_cases h : z * x = 1
  · rw [if_pos h, getLast?_cons_of_ne_nil _ hl]
  · rw [if_neg h, getLast?_cons_of_ne_nil _ hl, getLast?_cons_of_ne_nil _ hl]

/-! ### The back of a word, through the inverse -/

theorem exists_neWord {g : CoprodI G} (hg : g ≠ 1) :
    ∃ (i j : ι) (u : NeWord G i j), u.toWord = Word.equiv g ∧ u.prod = g := by
  have hne : Word.equiv g ≠ Word.empty := by
    intro h
    apply hg
    have hp := prod_equiv g
    rw [h, Word.prod_empty] at hp
    exact hp.symm
  obtain ⟨i, j, u, hu⟩ := NeWord.of_word (Word.equiv g) hne
  refine ⟨i, j, u, hu, ?_⟩
  have h2 : u.prod = (Word.equiv g).prod := by
    show u.toWord.prod = (Word.equiv g).prod
    rw [hu]
  rw [h2, prod_equiv]

theorem sylLength_eq_of_neWord {i j : ι} {u : NeWord G i j} {g : CoprodI G}
    (hu : u.toWord = Word.equiv g) : sylLength g = u.toList.length := by
  simp only [sylLength, ← hu]
  rfl

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem toList_length_inv {i j : ι} (u : NeWord G i j) :
    u.inv.toList.length = u.toList.length := by
  induction u with
  | @singleton i x hx => simp [NeWord.inv, NeWord.toList]
  | @append i j k l u₁ hne u₂ ih₁ ih₂ =>
      simp only [NeWord.inv, NeWord.toList, List.length_append, ih₁, ih₂]
      omega

theorem equiv_inv_of_neWord {i j : ι} {u : NeWord G i j} {g : CoprodI G}
    (hu : u.prod = g) : Word.equiv g⁻¹ = u.inv.toWord := by
  have h1 : u.inv.toWord.prod = g⁻¹ := by
    show u.inv.prod = g⁻¹
    rw [NeWord.inv_prod, hu]
  rw [← h1, equiv_prod]

/-- **Inversion preserves syllable length.** -/
theorem sylLength_inv (g : CoprodI G) : sylLength g⁻¹ = sylLength g := by
  by_cases hg : g = 1
  · subst hg; simp [sylLength]
  · obtain ⟨i, j, u, hu, hup⟩ := exists_neWord hg
    show (Word.equiv g⁻¹).toList.length = sylLength g
    rw [equiv_inv_of_neWord hup]
    show u.inv.toList.length = sylLength g
    rw [toList_length_inv, sylLength_eq_of_neWord hu]

/-- **The first letter of `g⁻¹` inverts the last letter of `g`.** -/
theorem head?_equiv_inv {i j : ι} {u : NeWord G i j} {g : CoprodI G}
    (hu : u.prod = g) :
    (Word.equiv g⁻¹).toList.head? = some ⟨j, (u.last)⁻¹⟩ := by
  rw [equiv_inv_of_neWord hu]
  show u.inv.toList.head? = _
  rw [NeWord.toList_head?, NeWord.inv_head]

/-- **Peeling the back letter.**  This is the front-peeling lemma read through
`g * (of y)⁻¹ = (of y * g⁻¹)⁻¹`. -/
theorem sylLength_mul_inv_last {i : ι} {y : G i} {g : CoprodI G}
    (hy : (Word.equiv g).toList.getLast? = some ⟨i, y⟩) :
    sylLength (g * (CoprodI.of y)⁻¹) + 1 = sylLength g := by
  have hg1 : g ≠ 1 := by
    intro h
    rw [h] at hy
    simp at hy
  obtain ⟨p, q, u, hu, hup⟩ := exists_neWord hg1
  have hlast : (Word.equiv g).toList.getLast? = some ⟨q, u.last⟩ := by
    rw [← hu]; exact NeWord.toList_getLast? u
  have hsig : (⟨q, u.last⟩ : (j : ι) × G j) = ⟨i, y⟩ :=
    Option.some.inj (hlast.symm.trans hy)
  -- inverting the last letter is a map of sigma types, so the index needs no
  -- substitution: `⟨q, u.last⟩ = ⟨i, y⟩` gives `⟨q, u.last⁻¹⟩ = ⟨i, y⁻¹⟩`
  have hhead : (Word.equiv g⁻¹).toList.head?
      = some (⟨i, y⁻¹⟩ : (j : ι) × G j) := by
    rw [head?_equiv_inv hup]
    exact congrArg some
      (congrArg (fun s : (j : ι) × G j => (⟨s.1, s.2⁻¹⟩ : (j : ι) × G j)) hsig)
  obtain ⟨l', hl'⟩ := exists_cons_of_head?_eq hhead
  have hpeel : sylLength (CoprodI.of (y⁻¹)⁻¹ * g⁻¹) = l'.length :=
    sylLength_of_smul_cancel hl'
  rw [inv_inv] at hpeel
  have hlen : sylLength g = l'.length + 1 := by
    rw [← sylLength_inv g]
    simp only [sylLength, hl', List.length_cons]
  have hrewrite : g * (CoprodI.of y)⁻¹ = (CoprodI.of y * g⁻¹)⁻¹ := by group
  rw [hrewrite, sylLength_inv, hpeel, hlen]

/-! ### Powers of a cyclically reduced word -/

/-- The reduced word spelling `u.prod ^ (n+1)`, for `u` whose first and last
letters lie in different factors. -/
def npow {i j : ι} (hij : i ≠ j) (u : NeWord G i j) : ℕ → NeWord G i j
  | 0 => u
  | (n + 1) => (npow hij u n).append hij.symm u

omit [DecidableEq ι] [(i : ι) → DecidableEq (G i)] in
theorem npow_prod {i j : ι} (hij : i ≠ j) (u : NeWord G i j) :
    ∀ n : ℕ, (npow hij u n).prod = u.prod ^ (n + 1)
  | 0 => by simp [npow]
  | (n + 1) => by
      rw [npow, NeWord.append_prod, npow_prod hij u n, ← pow_succ]

/-- **A cyclically reduced word of length at least two has infinite order.** -/
theorem pow_ne_one_of_ne {i j : ι} (hij : i ≠ j) (u : NeWord G i j) (n : ℕ) :
    u.prod ^ (n + 1) ≠ 1 := by
  rw [← npow_prod hij u n]
  exact FreeProductOrder.neWord_prod_ne_one _

/-! ### Cyclic reduction -/

/-- Conjugation commutes with taking powers.  Stated here because the
cyclic-reduction argument and its consumers in
`Sofic.OsinRelativeSmallCancellation` both spend it. -/
theorem conj_pow_eq {H : Type*} [Group H] (c a : H) (n : ℕ) :
    (c * a * c⁻¹) ^ n = c * a ^ n * c⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

/-- Conjugation reflects triviality. -/
theorem eq_one_of_conj_eq_one {H : Type*} [Group H] {c a : H}
    (h : c * a * c⁻¹ = 1) : a = 1 := by
  have h2 : c * a * c⁻¹ = c * 1 * c⁻¹ := by rw [h]; group
  exact mul_left_cancel (mul_right_cancel h2)

/-- **Cyclic reduction.**  Every element of a free product is conjugate to one
of exactly three kinds: the identity, a single syllable, or a word whose first
and last letters lie in different factors. -/
theorem exists_cyclicReduction (g : CoprodI G) :
    g = 1 ∨ (∃ (i : ι) (x : G i) (c : CoprodI G), g = c * CoprodI.of x * c⁻¹) ∨
      ∃ (i j : ι) (u : NeWord G i j) (c : CoprodI G),
        i ≠ j ∧ g = c * u.prod * c⁻¹ := by
  suffices h : ∀ (n : ℕ) (g : CoprodI G), sylLength g ≤ n →
      (g = 1 ∨ (∃ (i : ι) (x : G i) (c : CoprodI G), g = c * CoprodI.of x * c⁻¹) ∨
        ∃ (i j : ι) (u : NeWord G i j) (c : CoprodI G),
          i ≠ j ∧ g = c * u.prod * c⁻¹) by
    exact h (sylLength g) g le_rfl
  intro n
  induction n with
  | zero =>
      intro g hg
      exact Or.inl (sylLength_eq_zero_iff.mp (Nat.le_zero.mp hg))
  | succ n ih =>
      intro g hg
      by_cases hle : sylLength g ≤ n
      · exact ih g hle
      have hlen : sylLength g = n + 1 := by omega
      rcases hlist : (Word.equiv g).toList with _ | ⟨a, l⟩
      · refine Or.inl (sylLength_eq_zero_iff.mp ?_)
        simp only [sylLength, hlist, List.length_nil]
      rcases l with _ | ⟨b, l'⟩
      · -- one letter: the element is a single syllable
        have hprod : Word.prod (Word.equiv g) = CoprodI.of a.snd := by
          simp [Word.prod, hlist]
        refine Or.inr (Or.inl ⟨a.fst, a.snd, 1, ?_⟩)
        rw [one_mul, inv_one, mul_one, ← prod_equiv g]
        exact hprod
      -- at least two letters
      have hne1 : g ≠ 1 := by
        intro h
        rw [h] at hlist
        simp at hlist
      obtain ⟨p, q, u, hu, hup⟩ := exists_neWord hne1
      have hheadeq : (Word.equiv g).toList.head? = some ⟨p, u.head⟩ := by
        rw [← hu]; exact NeWord.toList_head? u
      have ha : a = (⟨p, u.head⟩ : (j : ι) × G j) := by
        have h1 : (a :: b :: l').head? = some ⟨p, u.head⟩ := by
          rw [← hlist]; exact hheadeq
        simpa using h1
      subst ha
      by_cases hpq : p = q
      · subst hpq
        -- first and last letters in the same factor: conjugate and shorten
        have hlasteq : (Word.equiv g).toList.getLast? = some ⟨_, u.last⟩ := by
          rw [← hu]; exact NeWord.toList_getLast? u
        have h1 : sylLength (CoprodI.of u.last * g) ≤ sylLength g :=
          sylLength_of_smul_le u.last hlist
        have h2 : (Word.equiv (CoprodI.of u.last * g)).toList.getLast?
            = some ⟨_, u.last⟩ :=
          (getLast?_of_smul u.last hlist (by simp)).trans hlasteq
        have h3 := sylLength_mul_inv_last h2
        have hshort :
            sylLength (CoprodI.of u.last * g * (CoprodI.of u.last)⁻¹) ≤ n := by
          omega
        have hgg : g = (CoprodI.of u.last)⁻¹ *
            (CoprodI.of u.last * g * (CoprodI.of u.last)⁻¹) * CoprodI.of u.last := by
          group
        rcases ih _ hshort with hone | ⟨k, z, c, hz⟩ | ⟨k, m, v, c, hkm, hv⟩
        · refine Or.inl ?_
          rw [hgg, hone]
          group
        · refine Or.inr (Or.inl ⟨k, z, (CoprodI.of u.last)⁻¹ * c, ?_⟩)
          rw [hgg, hz]
          group
        · refine Or.inr (Or.inr ⟨k, m, v, (CoprodI.of u.last)⁻¹ * c, hkm, ?_⟩)
          rw [hgg, hv]
          group
      · exact Or.inr (Or.inr ⟨p, q, u, 1, hpq, by
          rw [one_mul, inv_one, mul_one, hup]⟩)

/-- **Torsion in a free product is conjugate into a factor**, with the order
carried along.  This is the free-product case of the torsion clause of Osin's
small-cancellation theorem: the relator family is empty, so the quotient is
the free product itself. -/
theorem torsion_conj_into_factor {g : CoprodI G} {n : ℕ} (hn : 0 < n)
    (hgn : g ^ n = 1) :
    g = 1 ∨ ∃ (i : ι) (x : G i) (c : CoprodI G),
      x ^ n = 1 ∧ g = c * CoprodI.of x * c⁻¹ := by
  rcases exists_cyclicReduction g with h | ⟨i, x, c, hgc⟩ | ⟨i, j, u, c, hij, hgc⟩
  · exact Or.inl h
  · refine Or.inr ⟨i, x, c, ?_, hgc⟩
    have h1 : c * (CoprodI.of x) ^ n * c⁻¹ = 1 := by
      rw [← conj_pow_eq, ← hgc, hgn]
    have h2 : (CoprodI.of x) ^ n = 1 := eq_one_of_conj_eq_one h1
    rw [← map_pow] at h2
    have h3 : CoprodI.of (x ^ n) = CoprodI.of (1 : G i) := by
      rw [h2, map_one]
    exact CoprodI.of_injective i h3
  · exfalso
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : c * u.prod ^ (m + 1) * c⁻¹ = 1 := by
      rw [← conj_pow_eq, ← hgc, hgn]
    have h2 : u.prod ^ (m + 1) = 1 := eq_one_of_conj_eq_one h1
    exact pow_ne_one_of_ne hij u m h2

end Words

/-- **A free product of torsion-free groups is torsion-free.**

This is the `R = ∅` case of "a small-cancellation quotient of `U * H` stays
torsion-free", and it is unconditional. -/
theorem isPowerTorsionFree_coprodI {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] (h : ∀ i, IsPowerTorsionFree (G i)) :
    IsPowerTorsionFree (CoprodI G) := by
  classical
  intro g n hn hgn
  rcases torsion_conj_into_factor hn hgn with h1 | ⟨i, x, c, hx, rfl⟩
  · exact h1
  · rw [h i x n hn hx]
    simp

end FreeProductCyclic
end GroupApproximation
