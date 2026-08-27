import GroupApproximation.Sofic.GreendlingerCombinatorics

/-!
# Conjugating a cyclically reduced word by one letter

`Sofic/GreendlingerCombinatorics` lands the letters-and-closure layer of the
diagram-free attack on `GreendlingerGate` and names the next layers: the
palindromic conjugation normal form, then the one-relator Greendlinger
conclusion, then the minimal-expression descent.  This file is the crux of the
first of those.

## The step

The conjugation normal form asserts that a conjugate `g r g⁻¹` of a cyclically
reduced `r` spells out as `c ++ (a rotation of r) ++ invRev c`, with no
cancellation.  It is proved by induction on `g` one letter at a time, and the
whole content of the induction step is what a *single* letter can do:

* if `a` cancels neither end, the word `[a] ++ w ++ [a⁻¹]` is already reduced
  and the conjugator grows by one letter (`isReduced_conj_letter`);
* if `a` cancels the **head** of `w`, the two cancellations at the two ends
  leave a **rotation of `w` by one** (`mk_conj_head`);
* if `a` cancels the **tail**, they leave a rotation the other way
  (`mk_conj_last`);
* and for a cyclically reduced `w` the last two cannot happen together
  (`not_cancel_head_and_last`) --- that is precisely what cyclic reducedness
  buys, and it is why the rotation is well defined.

`conj_letter_cases` packages the trichotomy in the form the induction consumes.

## Why the cancelling cases are pure algebra

They need no reduction analysis at all.  If `w = x :: t` and `a = x⁻¹` then

`[a] ++ w ++ [a⁻¹] = [x⁻¹] ++ (x :: t) ++ [x]`,  which spells
`(mk [x])⁻¹ * (mk [x] * mk t) * mk [x] = mk t * mk [x] = mk (t ++ [x])`,

and `t ++ [x]` *is* `(x :: t).rotate 1`.  The same two lines, mirrored, give the
tail case.  Only the non-cancelling case touches `List.IsChain`, and there the
two junction conditions are exactly the two hypotheses.

Unconditional; nothing here depends on the gate.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The algebraic shape of a one-letter conjugate -/

theorem mk_singleton_inv (a : α × Bool) :
    (FreeGroup.mk [a])⁻¹ = FreeGroup.mk [invLetter a] := by
  rw [FreeGroup.inv_mk, invRev_singleton]

theorem mk_cons (x : α × Bool) (t : List (α × Bool)) :
    FreeGroup.mk (x :: t) = FreeGroup.mk [x] * FreeGroup.mk t :=
  (FreeGroup.mul_mk (L₁ := [x]) (L₂ := t)).symm

theorem mk_append_singleton (t : List (α × Bool)) (y : α × Bool) :
    FreeGroup.mk (t ++ [y]) = FreeGroup.mk t * FreeGroup.mk [y] := by
  rw [FreeGroup.mul_mk]

/-- A one-letter conjugate, read as a product. -/
theorem mk_conj_letter (a : α × Bool) (w : List (α × Bool)) :
    FreeGroup.mk ([a] ++ w ++ [invLetter a])
      = FreeGroup.mk [a] * FreeGroup.mk w * (FreeGroup.mk [a])⁻¹ := by
  rw [mk_singleton_inv, FreeGroup.mul_mk, FreeGroup.mul_mk]

/-! ## The two cancelling cases are rotations -/

/-- Rotating `t ++ [y]` by `t.length` moves the last letter to the front. -/
theorem rotate_append_singleton (t : List (α × Bool)) (y : α × Bool) :
    (t ++ [y]).rotate t.length = [y] ++ t := by
  have hle : t.length ≤ (t ++ [y]).length := by simp
  rw [List.rotate_eq_drop_append_take hle]
  simp

/-- **Cancelling at the head rotates forward by one.** -/
theorem mk_conj_head (x : α × Bool) (t : List (α × Bool)) :
    FreeGroup.mk ([invLetter x] ++ (x :: t) ++ [invLetter (invLetter x)])
      = FreeGroup.mk ((x :: t).rotate 1) := by
  have hrot : (x :: t).rotate 1 = t ++ [x] := by simp
  have hinv : (FreeGroup.mk [x])⁻¹ = FreeGroup.mk [invLetter x] :=
    mk_singleton_inv x
  calc FreeGroup.mk ([invLetter x] ++ (x :: t) ++ [invLetter (invLetter x)])
      = FreeGroup.mk [invLetter x] * FreeGroup.mk (x :: t)
          * (FreeGroup.mk [invLetter x])⁻¹ := mk_conj_letter _ _
    _ = FreeGroup.mk t * FreeGroup.mk [x] := by
        rw [mk_cons x t, ← hinv]
        group
    _ = FreeGroup.mk ((x :: t).rotate 1) := by
        rw [hrot, mk_append_singleton]

/-- **Cancelling at the tail rotates the other way.** -/
theorem mk_conj_last (t : List (α × Bool)) (y : α × Bool) :
    FreeGroup.mk ([y] ++ (t ++ [y]) ++ [invLetter y])
      = FreeGroup.mk ((t ++ [y]).rotate t.length) := by
  rw [rotate_append_singleton, mk_conj_letter, mk_append_singleton,
    ← FreeGroup.mul_mk]
  group

/-! ## Cyclic reducedness forbids cancelling at both ends -/

/-- **A cyclically reduced word cannot cancel at both ends by the same letter.**
This is exactly what cyclic reducedness is for: it makes the rotation produced
by a one-letter conjugation unambiguous. -/
theorem not_cancel_head_and_last {w : List (α × Bool)}
    (hw : FreeGroup.IsCyclicallyReduced w) {a x : α × Bool}
    (hhead : w.head? = some x) (hcancel : a = invLetter x)
    (hlast : w.getLast? = some a) : False := by
  have hrel := hw.2 a hlast x hhead
  have hne : x ≠ invLetter a := isReduced_step_iff.mp hrel
  exact hne (by rw [hcancel, invLetter_invLetter])

/-! ## The non-cancelling case is reduced -/

/-- **If the letter cancels neither end the conjugate is already reduced.** -/
theorem isReduced_conj_letter {w : List (α × Bool)}
    (hw : FreeGroup.IsReduced w) (hne : w ≠ []) (a : α × Bool)
    (hhead : ∀ y ∈ w.head?, y ≠ invLetter a)
    (hlast : ∀ x ∈ w.getLast?, x ≠ a) :
    FreeGroup.IsReduced ([a] ++ w ++ [invLetter a]) := by
  refine List.isChain_append.mpr ⟨?_, FreeGroup.IsReduced.singleton, ?_⟩
  · refine List.isChain_append.mpr ⟨FreeGroup.IsReduced.singleton, hw, ?_⟩
    intro p hp q hq
    have hpa : p = a := (by simpa using hp : a = p).symm
    subst hpa
    exact isReduced_step_iff.mpr (hhead q hq)
  · intro p hp q hq
    have hqa : q = invLetter a := (by simpa using hq : invLetter a = q).symm
    subst hqa
    have hp' : p ∈ w.getLast? := by
      rwa [List.getLast?_append_of_ne_nil _ hne] at hp
    refine isReduced_step_iff.mpr ?_
    intro hcon
    exact hlast p hp' (invLetter_injective hcon).symm

/-! ## The trichotomy the induction consumes -/

/-- **One-letter conjugation of a cyclically reduced word.**  Either the
conjugate is already reduced -- so the conjugator grows by one letter and the
rotation is unchanged -- or it is a rotation of the word itself. -/
theorem conj_letter_cases {w : List (α × Bool)}
    (hw : FreeGroup.IsCyclicallyReduced w) (hne : w ≠ []) (a : α × Bool) :
    FreeGroup.IsReduced ([a] ++ w ++ [invLetter a]) ∨
      ∃ k : ℕ, FreeGroup.mk ([a] ++ w ++ [invLetter a])
        = FreeGroup.mk (w.rotate k) := by
  classical
  by_cases hhead : w.head? = some (invLetter a)
  · -- the letter cancels the head: rotate forward by one
    refine Or.inr ⟨1, ?_⟩
    cases w with
    | nil => exact absurd rfl hne
    | cons c t =>
        have hc : c = invLetter a := by simpa using hhead
        subst hc
        have := mk_conj_head (invLetter a) t
        rwa [invLetter_invLetter] at this
  · by_cases hlast : w.getLast? = some a
    · -- the letter cancels the tail: rotate the other way
      refine Or.inr ⟨w.dropLast.length, ?_⟩
      have hy : w.getLast hne = a := by
        have hsome := List.getLast?_eq_some_getLast hne
        rw [hlast] at hsome
        exact (Option.some_inj.mp hsome).symm
      have hrw : w.dropLast ++ [a] = w := by
        rw [← hy]
        exact List.dropLast_append_getLast hne
      calc FreeGroup.mk ([a] ++ w ++ [invLetter a])
          = FreeGroup.mk ([a] ++ (w.dropLast ++ [a]) ++ [invLetter a]) := by
            rw [hrw]
        _ = FreeGroup.mk ((w.dropLast ++ [a]).rotate w.dropLast.length) :=
            mk_conj_last w.dropLast a
        _ = FreeGroup.mk (w.rotate w.dropLast.length) := by rw [hrw]
    · -- neither end cancels
      refine Or.inl (isReduced_conj_letter hw.isReduced hne a ?_ ?_)
      · intro y hy hcon
        apply hhead
        rw [← hcon]
        exact hy
      · intro x hx hcon
        apply hlast
        rw [← hcon]
        exact hx

end SmallCancellationRouter
end GroupApproximation
