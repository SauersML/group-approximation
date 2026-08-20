import GroupApproximation.Higman.Program

/-!
# Raw words: the calculus `RecursivePresentation` needs

`Higman.Program` defines a recursive presentation as a countable generating
family `gen : ℕ → A` together with recursive enumerability of

    { w : RawWord | evalRaw gen w = 1 } .

Both halves of that definition need a small amount of ordinary algebra before
any computability argument can start: that `evalRaw` really is word
evaluation (it is multiplicative on concatenation and inverts on formal
inverses), that its image is exactly the generated subgroup (so `spans` is
equivalent to *every element is a word*), and that it commutes with
homomorphisms (so a coordinate of a word is the word of the coordinates).

This file is that calculus, and then the algebraic half of `Program`'s split
**(B1)**: a raw word is trivial in the restricted direct product
`Monsters.CodedDirectSum` exactly when each of its coordinate evaluations is
trivial in the corresponding coded group.  What remains of (B1) after this
file is purely computability --- that the block of a generator is computable
from its index, that only the finitely many blocks occurring in `w` have to be
checked (`evalRaw_eq_one_of_letters` is what makes that finiteness true), and
that each check is recursively enumerable by
`Computability.WordProblemRE.rePred_wordProblemPred`.  None of that is here.

Nothing in this file is specific to the absorber except the last two
declarations, and nothing in it mentions computability at all.
-/

namespace GroupApproximation
namespace Higman

variable {A B : Type} [Group A] [Group B]

/-! ## 1.  `evalRaw` is a word evaluation -/

@[simp] theorem evalRaw_append (x : ℕ → A) (v w : RawWord) :
    evalRaw x (v ++ w) = evalRaw x v * evalRaw x w := by
  induction v with
  | nil => simp
  | cons p v ih =>
      obtain ⟨i, b⟩ := p
      simp [ih, mul_assoc]

/-- The formal inverse of a raw word. -/
def invRaw : RawWord → RawWord
  | [] => []
  | (i, b) :: w => invRaw w ++ [(i, !b)]

@[simp] theorem evalRaw_invRaw (x : ℕ → A) (w : RawWord) :
    evalRaw x (invRaw w) = (evalRaw x w)⁻¹ := by
  induction w with
  | nil => simp [invRaw]
  | cons p w ih =>
      obtain ⟨i, b⟩ := p
      cases b <;> simp [invRaw, ih, mul_inv_rev]

/-! ## 2.  The image of `evalRaw` is the generated subgroup -/

theorem evalRaw_mem_closure (x : ℕ → A) (w : RawWord) :
    evalRaw x w ∈ Subgroup.closure (Set.range x) := by
  induction w with
  | nil => simp
  | cons p w ih =>
      obtain ⟨i, b⟩ := p
      refine Subgroup.mul_mem _ ?_ ih
      cases b with
      | false =>
          simpa using Subgroup.inv_mem _
            (Subgroup.subset_closure (k := Set.range x) ⟨i, rfl⟩)
      | true =>
          simpa using Subgroup.subset_closure (k := Set.range x) ⟨i, rfl⟩

theorem exists_evalRaw_of_mem_closure (x : ℕ → A) {g : A}
    (hg : g ∈ Subgroup.closure (Set.range x)) :
    ∃ w : RawWord, evalRaw x w = g := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨[(i, true)], by simp⟩
  | one => exact ⟨[], rfl⟩
  | mul y z _ _ ihy ihz =>
      obtain ⟨v, rfl⟩ := ihy
      obtain ⟨w, rfl⟩ := ihz
      exact ⟨v ++ w, by simp⟩
  | inv y _ ihy =>
      obtain ⟨v, rfl⟩ := ihy
      exact ⟨invRaw v, by simp⟩

theorem mem_closure_iff_exists_evalRaw (x : ℕ → A) (g : A) :
    g ∈ Subgroup.closure (Set.range x) ↔ ∃ w : RawWord, evalRaw x w = g :=
  ⟨exists_evalRaw_of_mem_closure x, by
    rintro ⟨w, rfl⟩
    exact evalRaw_mem_closure x w⟩

/-- **The `spans` field of a `RecursivePresentation`, unpacked.**  A family
generates exactly when every element is the value of a raw word. -/
theorem spans_iff_forall_exists_evalRaw (x : ℕ → A) :
    Subgroup.closure (Set.range x) = ⊤ ↔
      ∀ g : A, ∃ w : RawWord, evalRaw x w = g := by
  rw [Subgroup.eq_top_iff']
  exact forall_congr' fun g => mem_closure_iff_exists_evalRaw x g

/-! ## 3.  Transport along homomorphisms -/

/-- **A homomorphism of a word value is the word value of the images.**  This
is what turns a coordinate of a product into a product of coordinates, and it
is the only thing the coordinatewise criterion below needs. -/
@[simp] theorem map_evalRaw (f : A →* B) (x : ℕ → A) (w : RawWord) :
    f (evalRaw x w) = evalRaw (fun n ↦ f (x n)) w := by
  induction w with
  | nil => simp
  | cons p w ih =>
      obtain ⟨i, b⟩ := p
      cases b <;> simp [ih]

/-- **Only the letters occurring in `w` matter.**  If every generator used by
`w` is trivial then so is its value.  This is the finiteness that lets the
coordinatewise criterion be checked on the finitely many blocks that actually
occur. -/
theorem evalRaw_eq_one_of_letters (x : ℕ → A) (w : RawWord)
    (h : ∀ p ∈ w, x p.1 = 1) : evalRaw x w = 1 := by
  induction w with
  | nil => simp
  | cons p w ih =>
      obtain ⟨i, b⟩ := p
      have h1 : x i = 1 := h (i, b) (by simp)
      have h2 : evalRaw x w = 1 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      cases b <;> simp [h1, h2]

/-! ## 4.  The algebraic half of `Program`'s split (B1) -/

open GroupApproximation.Monsters

/-- An element of the restricted direct product is trivial exactly when every
coordinate of it is.  `Monsters.codedEval` is the coordinate. -/
theorem codedDirectSum_eq_one_iff (g : CodedDirectSum) :
    g = 1 ↔ ∀ c : FinitePresentationCode, codedEval c g = 1 := by
  constructor
  · intro h c
    rw [h, map_one]
  · intro h
    apply Multiplicative.toAdd.injective
    apply DFinsupp.ext
    intro c
    -- `codedEval c` is `toMul ∘ (· c) ∘ toAdd` with `map_one' := rfl`, so both
    -- sides of `h c` are already the images the injectivity wants; ascribing
    -- them saves the simp set from having to see through `CodedDirectSum`.
    have hc : Additive.toMul ((Multiplicative.toAdd g) c)
        = Additive.toMul ((Multiplicative.toAdd (1 : CodedDirectSum)) c) := h c
    exact Additive.toMul.injective hc

/-- **(B1), algebraic half.**  A raw word is trivial in the restricted direct
product exactly when, in every coded group, the word of the coordinates is
trivial.

What is left of (B1) is that the right-hand side is recursively enumerable:
the coordinate family `fun n ↦ codedEval c (gen n)` must be computable from
`c`, only the finitely many `c` occurring as blocks of `w` can contribute
(`evalRaw_eq_one_of_letters`), and each remaining condition is the word
problem of a finite presentation, which is recursively enumerable by
`Computability.WordProblemRE.rePred_wordProblemPred`. -/
theorem evalRaw_codedDirectSum_eq_one_iff (x : ℕ → CodedDirectSum)
    (w : RawWord) :
    evalRaw x w = 1 ↔
      ∀ c : FinitePresentationCode,
        evalRaw (fun n ↦ codedEval c (x n)) w = 1 := by
  rw [codedDirectSum_eq_one_iff]
  exact forall_congr' fun c => by rw [map_evalRaw]

end Higman
end GroupApproximation
