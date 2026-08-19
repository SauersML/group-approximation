import GroupApproximation.Sofic.GreendlingerConjugation

/-!
# The palindromic conjugation normal form

`GreendlingerCombinatorics` lands the letters-and-closure layer of the
diagram-free attack on `GreendlingerGate`, and names the next layer: the
palindromic conjugation normal form.  `GreendlingerConjugation` proves what one
letter can do to a cyclically reduced word.  This file runs the induction and
closes that layer.

## The statement

For `r` cyclically reduced and nonempty, **every** conjugate of `mk r` is
spelled by a *reduced* word of the shape

`palindrome c m = c ++ m ++ invRev c`,  with `m` a rotation of `r`.

So a conjugate of a relator carries a whole cyclic permutation of that relator
as a contiguous subword, and carries it with no cancellation.  That is the
one-relator case of the Greendlinger conclusion, and it is what the general case
degenerates to when the minimal expression has a single factor.

## The induction

On the conjugator, one letter at a time, maintaining the shape.  Adding a letter
`a` to the front of the conjugator conjugates the palindrome by `a`, and there
are exactly two regimes:

* **the conjugator is nonempty**, `c = d :: c'`.  Then the palindrome begins
  with `d` and ends with `invLetter d`, so `a` cancels at both ends or at
  neither -- never at one.  Cancelling *shrinks* the conjugator to `c'` and
  leaves the rotation alone (`mk_conj_palindrome_cancel`, pure `mk`-algebra);
  not cancelling *grows* it to `a :: c` and the result is reduced.
* **the conjugator is empty**, so the palindrome *is* the rotation, which is
  cyclically reduced.  This is exactly `conj_letter_cases`: either the result is
  reduced, with conjugator `[a]`, or it is a further rotation, with conjugator
  still empty.

Cyclic reducedness is used in precisely one place, the empty-conjugator regime,
where it forbids cancelling at both ends and so keeps the rotation well defined.

Unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Palindromes -/

/-- The shape a conjugate of a cyclically reduced word takes: a rotation with a
conjugator wrapped around it. -/
def palindrome (c m : List (α × Bool)) : List (α × Bool) :=
  c ++ m ++ FreeGroup.invRev c

@[simp] theorem palindrome_nil (m : List (α × Bool)) :
    palindrome [] m = m := by
  simp [palindrome]

theorem palindrome_cons (d : α × Bool) (c m : List (α × Bool)) :
    palindrome (d :: c) m = [d] ++ palindrome c m ++ [invLetter d] := by
  unfold palindrome
  rw [invRev_cons]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem mk_palindrome (c m : List (α × Bool)) :
    FreeGroup.mk (palindrome c m)
      = FreeGroup.mk c * FreeGroup.mk m * (FreeGroup.mk c)⁻¹ := by
  rw [FreeGroup.inv_mk]
  unfold palindrome
  rw [FreeGroup.mul_mk, FreeGroup.mul_mk]

theorem head?_palindrome_cons (d : α × Bool) (c m : List (α × Bool)) :
    (palindrome (d :: c) m).head? = some d := by
  rw [palindrome_cons]
  rfl

theorem getLast?_palindrome_cons (d : α × Bool) (c m : List (α × Bool)) :
    (palindrome (d :: c) m).getLast? = some (invLetter d) := by
  rw [palindrome_cons, List.getLast?_concat]

theorem palindrome_ne_nil {c m : List (α × Bool)} (hm : m ≠ []) :
    palindrome c m ≠ [] := by
  cases c with
  | nil => simpa using hm
  | cons d c' =>
      rw [palindrome_cons]
      simp

/-- Being reduced is inherited by contiguous subwords. -/
theorem isReduced_of_infix {L₁ L₂ : List (α × Bool)} (h : L₁ <:+: L₂)
    (hred : FreeGroup.IsReduced L₂) : FreeGroup.IsReduced L₁ := by
  obtain ⟨s, t, rfl⟩ := h
  exact (List.isChain_append.mp (List.isChain_append.mp hred).1).2.1

theorem isReduced_palindrome_of_cons {d : α × Bool} {c m : List (α × Bool)}
    (h : FreeGroup.IsReduced (palindrome (d :: c) m)) :
    FreeGroup.IsReduced (palindrome c m) :=
  isReduced_of_infix ⟨[d], [invLetter d], (palindrome_cons d c m).symm⟩ h

/-! ## Conjugating a palindrome with nonempty conjugator -/

/-- **Cancelling shrinks the conjugator.**  Pure `mk`-algebra: the letter that
cancels the head cancels the tail at the same time, and what is left is the
palindrome with one letter peeled off. -/
theorem mk_conj_palindrome_cancel (d : α × Bool) (c m : List (α × Bool)) :
    FreeGroup.mk ([invLetter d] ++ palindrome (d :: c) m
        ++ [invLetter (invLetter d)])
      = FreeGroup.mk (palindrome c m) := by
  rw [mk_conj_letter, palindrome_cons, mk_conj_letter, ← mk_singleton_inv]
  group

/-! ## The normal form -/

/-- **The palindromic conjugation normal form.**  Every conjugate of a
cyclically reduced nonempty word is spelled by a reduced palindrome around a
rotation of it.

In particular a conjugate of a relator contains a full cyclic permutation of
that relator as a contiguous subword, with no cancellation. -/
theorem exists_conjugation_normalForm {r : List (α × Bool)}
    (hr : FreeGroup.IsCyclicallyReduced r) (hrne : r ≠ [])
    (L : List (α × Bool)) :
    ∃ (c : List (α × Bool)) (k : ℕ),
      FreeGroup.IsReduced (palindrome c (r.rotate k)) ∧
        FreeGroup.mk L * FreeGroup.mk r * (FreeGroup.mk L)⁻¹
          = FreeGroup.mk (palindrome c (r.rotate k)) := by
  classical
  induction L with
  | nil =>
      refine ⟨[], 0, ?_, ?_⟩
      · simpa using hr.isReduced
      · rw [palindrome_nil, List.rotate_zero, ← FreeGroup.one_eq_mk]
        group
  | cons a L ih =>
      obtain ⟨c, k, hred, heq⟩ := ih
      have hrotne : r.rotate k ≠ [] := fun h => hrne (List.rotate_eq_nil_iff.mp h)
      -- the inductive step conjugates the palindrome by one letter
      have hconj : FreeGroup.mk (a :: L) * FreeGroup.mk r
            * (FreeGroup.mk (a :: L))⁻¹
          = FreeGroup.mk ([a] ++ palindrome c (r.rotate k) ++ [invLetter a]) := by
        rw [mk_conj_letter, ← heq, mk_cons]
        group
      cases c with
      | nil =>
          -- the palindrome *is* the rotation, which is cyclically reduced
          have hcyc : FreeGroup.IsCyclicallyReduced (r.rotate k) :=
            isCyclicallyReduced_rotate hr k
          rcases conj_letter_cases hcyc hrotne a with hcase | ⟨j, hcase⟩
          · refine ⟨[a], k, ?_, ?_⟩
            · rw [palindrome_cons, palindrome_nil]
              exact hcase
            · rw [hconj]
              exact (congrArg FreeGroup.mk
                (palindrome_cons a [] (r.rotate k))).symm
          · refine ⟨[], k + j, ?_, ?_⟩
            · rw [palindrome_nil]
              exact (isCyclicallyReduced_rotate hr (k + j)).isReduced
            · rw [hconj, palindrome_nil, ← List.rotate_rotate]
              exact hcase
      | cons d c' =>
          by_cases hcancel : a = invLetter d
          · -- cancelling shrinks the conjugator
            refine ⟨c', k, isReduced_palindrome_of_cons hred, ?_⟩
            rw [hconj, hcancel]
            exact mk_conj_palindrome_cancel d c' (r.rotate k)
          · -- no cancellation: the conjugator grows
            refine ⟨a :: d :: c', k, ?_, ?_⟩
            · rw [palindrome_cons]
              refine isReduced_conj_letter hred (palindrome_ne_nil hrotne) a ?_ ?_
              · intro y hy
                rw [head?_palindrome_cons] at hy
                have hyd : y = d := by simpa using hy
                subst hyd
                intro hcon
                exact hcancel (by rw [hcon, invLetter_invLetter])
              · intro x hx
                rw [getLast?_palindrome_cons] at hx
                have hxd : x = invLetter d := by simpa using hx
                subst hxd
                exact fun hcon => hcancel hcon.symm
            · rw [hconj]
              exact (congrArg FreeGroup.mk
                (palindrome_cons a (d :: c') (r.rotate k))).symm

end SmallCancellationRouter
end GroupApproximation
