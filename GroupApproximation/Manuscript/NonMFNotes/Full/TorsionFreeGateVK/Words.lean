import GroupApproximation.Sofic.GreendlingerCombinatorics

/-!
# Reduced words are never their own mirror

Word lemmas for the reduction of minimal van Kampen diagrams (Lyndon–Schupp,
Ch. V §2, Lemma 2.1): a face of a reduced diagram is never glued to itself as a
mirror, because a nonempty reduced word is never a cyclic rotation of its formal
inverse.

* `not_isReduced_append_inv`: an adjacent cancelling pair spoils reducedness;
* `eq_nil_of_isReduced_of_eq_invRev`: a reduced word equal to its formal inverse is
  empty;
* `ne_invRev_swap`: a nonempty reduced word `A ++ B` is not `invRev (B ++ A)`.

Part of thm:torsionfree (non_mf_group_notes.tex), L7 milestone 1, WO NN07a-A.
-/

namespace GroupApproximation.Full.NN07a.VK

open GroupApproximation.SmallCancellationRouter

universe u

variable {α : Type u}

/-- A letter is never its own formal inverse. -/
theorem invLetter_ne_self (c : α × Bool) : invLetter c ≠ c := by
  obtain ⟨x, b⟩ := c
  cases b <;> simp [invLetter]

/-- An adjacent cancelling pair `a a⁻¹` spoils reducedness. -/
theorem not_isReduced_append_inv (s t : List (α × Bool)) (a : α × Bool) :
    ¬ FreeGroup.IsReduced (s ++ a :: invLetter a :: t) := by
  intro h
  have h' : List.IsChain (fun x y : α × Bool => x.1 = y.1 → x.2 = y.2)
      (s ++ a :: invLetter a :: t) := h
  have hstep : a.1 = (invLetter a).1 → a.2 = (invLetter a).2 :=
    (List.isChain_append_cons_cons.mp h').2.1
  exact (isReduced_step_iff.mp hstep) rfl

/-- An adjacent cancelling pair `a⁻¹ a` spoils reducedness. -/
theorem not_isReduced_append_inv' (s t : List (α × Bool)) (a : α × Bool) :
    ¬ FreeGroup.IsReduced (s ++ invLetter a :: a :: t) := by
  have h := not_isReduced_append_inv s t (invLetter a)
  rwa [invLetter_invLetter] at h

/-- **A reduced word equal to its formal inverse is empty** (by induction on the
length, peeling the first and last letters). -/
theorem eq_nil_of_isReduced_of_eq_invRev :
    ∀ (n : ℕ) (X : List (α × Bool)), X.length = n → FreeGroup.IsReduced X →
      X = FreeGroup.invRev X → X = [] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hX hinv
  rcases X with _ | ⟨a, Y⟩
  · rfl
  · exfalso
    rcases List.eq_nil_or_concat Y with hY | ⟨Y', b, hY⟩
    · subst hY
      rw [invRev_singleton] at hinv
      exact invLetter_ne_self a (List.cons.inj hinv).1.symm
    · rw [List.concat_eq_append] at hY
      subst hY
      rw [GroupApproximation.SmallCancellationRouter.invRev_cons, FreeGroup.invRev_append,
        invRev_singleton, List.singleton_append, List.cons_append] at hinv
      obtain ⟨-, hrest⟩ := List.cons.inj hinv
      obtain ⟨hY', hb⟩ := List.append_inj' hrest rfl
      have hYred : FreeGroup.IsReduced Y' := hX.infix ⟨[a], [b], by simp⟩
      have hn' := hn
      simp only [List.length_cons, List.length_append, List.length_singleton] at hn'
      have hlen : Y'.length < n := by omega
      have hnil : Y' = [] := ih Y'.length hlen Y' rfl hYred hY'
      subst hnil
      have hb' : b = invLetter a := (List.cons.inj hb).1
      subst hb'
      exact not_isReduced_append_inv [] [] a hX

/-- **A nonempty reduced word is not a mirror of its own rotation**:
`A ++ B ≠ invRev (B ++ A)`. -/
theorem ne_invRev_swap {A B : List (α × Bool)} (hred : FreeGroup.IsReduced (A ++ B))
    (hne : A ++ B ≠ []) : A ++ B ≠ FreeGroup.invRev (B ++ A) := by
  intro h
  rw [FreeGroup.invRev_append] at h
  obtain ⟨hA, hB⟩ := List.append_inj h FreeGroup.invRev_length.symm
  have hA0 : A = [] :=
    eq_nil_of_isReduced_of_eq_invRev A.length A rfl (hred.infix ⟨[], B, by simp⟩) hA
  have hB0 : B = [] :=
    eq_nil_of_isReduced_of_eq_invRev B.length B rfl (hred.infix ⟨A, [], by simp⟩) hB
  exact hne (by simp only [hA0, hB0, List.append_nil])

end GroupApproximation.Full.NN07a.VK
