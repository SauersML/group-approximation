import GroupApproximation.Sofic.GreendlingerDehnCritical

/-!
# Free reduction, discharged against swap closure

`GreendlingerDehn` leaves the gate at `DehnReduceClosed` --- Dehn-reducibility
survives free reduction --- and `GreendlingerDehnCritical` splits that statement
into the configurations a critical-pair analysis produces.  This file runs the
analysis for the *free* half and closes it: every configuration of a cancelling
pair against the first step of a derivation is settled, and what is left over is
swap closure and nothing else.

  `dehnReducible_delete_pair` --- one cancellation, at one stage of the induction
  `freeClosedBelow_succ` --- the stage passes to the next
  `dehnFreeClosed_of_dehnSwapClosed`, `greendlingerConclusion_of_dehnSwapClosed`

## The analysis

The induction is on word length, and it is legitimate because every step of the
system strictly shortens its word (`DehnStep.length_lt`) --- the free rule by two
letters, the Dehn rule by the length it saves.  Given a cancelling pair inside a
reducible word, the first step of a derivation is either free or a Dehn step, and
the two are handled quite differently.

**A free first step** never needs the configuration analysis.  Mathlib's diamond
lemma for free reduction (`FreeGroup.Red.Step.diamond`) already says that two
deletions out of one word either produce the same word or reconverge in one
further deletion each; in the first case there is nothing to prove, and in the
second `FreeClosedBelow` carries reducibility to the meeting word, from which the
shortened word reaches it in a single free step.

**A Dehn first step** is where the configurations matter, and
`pair_occurrence_cases` enumerates them: the step's occurrence lies strictly
right of the pair, strictly left of it, ends at its first letter, begins at its
second, or covers both.  Then

* **disjoint** (either side) --- the step and the deletion commute.
  `FreeClosedBelow` deletes the pair from the step's output, and the step is
  replayed on the shortened word.
* **covering** --- impossible.  The occurrence sits inside a cyclically reduced
  relator, so it is reduced and cannot contain a letter beside its inverse
  (`not_cancel_in_relator`).  This is the only place the relators' hypothesis is
  used.
* **edge, either side** --- the step's output and the shortened word are related
  by a `DehnSwap`, by `dehnSwap_of_straddle_right` and
  `dehnSwap_of_straddle_left`: the pair takes one letter of the occurrence with
  it, and putting that letter on the other side of the split is the same relator
  read one place over, or rotated by one letter.  This is the only place swap
  closure is used, and it is used at the step's output, which is again strictly
  shorter.

The edge cases are the reason `DehnSwap` was defined without a length condition.
For a *step* the passage across the edge fails by exactly the two letters that
the boundary of the naive analysis stalls on; for a swap it is free.

Unconditional except for the cyclically-reduced hypothesis on the relators and
the swap closure that is passed in.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Steps, inverted and measured -/

/-- **A step shortens its word.**  The free rule deletes two letters, and the
Dehn rule replaces a block by a strictly shorter one.  This is what makes the
induction on length below well-founded. -/
theorem DehnStep.length_lt {R : Set (List (α × Bool))} {W W' : List (α × Bool)}
    (h : DehnStep R W W') : W'.length < W.length := by
  cases h with
  | free A B x =>
      simp only [List.length_append, List.length_cons]
      omega
  | dehn A B u v r _ hsplit hlong =>
      simp only [List.length_append, FreeGroup.invRev_length]
      rw [hsplit, List.length_append] at hlong
      omega

/-- **The two rules, as data.**  Inverting the inductive family once and for all
keeps the case analysis below free of index unification. -/
theorem dehnStep_iff {R : Set (List (α × Bool))} {W W' : List (α × Bool)} :
    DehnStep R W W' ↔
      (∃ A B : List (α × Bool), ∃ x : α × Bool,
        W = A ++ (x :: invLetter x :: B) ∧ W' = A ++ B) ∨
      (∃ A B u v r : List (α × Bool), r ∈ symmetrization R ∧ r = u ++ v ∧
        r.length < 2 * u.length ∧
        W = A ++ (u ++ B) ∧ W' = A ++ (FreeGroup.invRev v ++ B)) := by
  constructor
  · intro h
    cases h with
    | free A B x => exact Or.inl ⟨A, B, x, rfl, rfl⟩
    | dehn A B u v r hr hsplit hlong =>
        exact Or.inr ⟨A, B, u, v, r, hr, hsplit, hlong, rfl, rfl⟩
  · rintro (⟨A, B, x, rfl, rfl⟩ | ⟨A, B, u, v, r, hr, hsplit, hlong, rfl, rfl⟩)
    · exact DehnStep.free A B x
    · exact DehnStep.dehn A B u v r hr hsplit hlong

/-! ## Where an occurrence sits relative to a cancelling pair -/

/-- **The five configurations.**  A word carrying both a two-letter block at
position `|A|` and a nonempty occurrence `Q` at position `|C|` realizes exactly
one of: `Q` strictly to the right of the block, strictly to its left, ending at
its first letter, beginning at its second, or covering both letters.

Nothing here is about free groups; it is the combinatorics of two occurrences in
one word. -/
theorem pair_occurrence_cases {β : Type*} {A B C D Q : List β} {x y : β}
    (hQne : Q ≠ []) (h : A ++ (x :: y :: B) = C ++ (Q ++ D)) :
    (∃ e, C = A ++ (x :: y :: e) ∧ B = e ++ (Q ++ D))
      ∨ (∃ e, A = C ++ (Q ++ e) ∧ D = e ++ (x :: y :: B))
      ∨ (∃ e, Q = e ++ [x] ∧ A = C ++ e ∧ D = y :: B)
      ∨ (∃ e, Q = y :: e ∧ C = A ++ [x] ∧ B = e ++ D)
      ∨ (∃ e f, Q = e ++ (x :: y :: f) ∧ A = C ++ e ∧ B = f ++ D) := by
  rcases List.append_eq_append_iff.mp h with ⟨as, hC, hsp⟩ | ⟨bs, hA, hsp⟩
  · -- the occurrence starts at or after the pair
    rcases as with _ | ⟨a, as'⟩
    · -- it starts exactly at the pair
      rw [List.nil_append] at hsp
      rcases Q with _ | ⟨q, qs⟩
      · exact absurd rfl hQne
      · rw [List.cons_append] at hsp
        simp only [List.cons.injEq] at hsp
        obtain ⟨hq, hsp2⟩ := hsp
        rcases qs with _ | ⟨q', qs'⟩
        · -- the occurrence is the pair's first letter alone
          rw [List.nil_append] at hsp2
          refine Or.inr (Or.inr (Or.inl ⟨[], ?_, ?_, hsp2.symm⟩))
          · rw [List.nil_append, hq]
          · simp [hC]
        · -- the occurrence covers the pair
          rw [List.cons_append] at hsp2
          simp only [List.cons.injEq] at hsp2
          obtain ⟨hq', hsp3⟩ := hsp2
          refine Or.inr (Or.inr (Or.inr (Or.inr ⟨[], qs', ?_, ?_, hsp3⟩)))
          · rw [List.nil_append, hq, hq']
          · simp [hC]
    · rcases as' with _ | ⟨b, as''⟩
      · -- it starts at the pair's second letter
        rw [List.cons_append, List.nil_append] at hsp
        simp only [List.cons.injEq] at hsp
        obtain ⟨ha, hsp2⟩ := hsp
        rcases Q with _ | ⟨q, qs⟩
        · exact absurd rfl hQne
        · rw [List.cons_append] at hsp2
          simp only [List.cons.injEq] at hsp2
          obtain ⟨hq, hsp3⟩ := hsp2
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨qs, ?_, ?_, hsp3⟩)))
          · rw [hq]
          · rw [hC, ha]
      · -- it starts strictly after the pair
        rw [List.cons_append, List.cons_append] at hsp
        simp only [List.cons.injEq] at hsp
        obtain ⟨ha, hb, hsp2⟩ := hsp
        refine Or.inl ⟨as'', ?_, hsp2⟩
        rw [hC, ha, hb]
  · -- the occurrence starts at or before the pair
    rcases List.append_eq_append_iff.mp hsp with ⟨as, hbs, hD⟩ | ⟨cs, hQ, hsp2⟩
    · refine Or.inr (Or.inl ⟨as, ?_, hD⟩)
      rw [hA, hbs]
    · rcases cs with _ | ⟨c, cs'⟩
      · rw [List.nil_append] at hsp2
        refine Or.inr (Or.inl ⟨[], ?_, ?_⟩)
        · rw [hA, hQ, List.append_nil, List.append_nil]
        · rw [List.nil_append, hsp2]
      · rw [List.cons_append] at hsp2
        simp only [List.cons.injEq] at hsp2
        obtain ⟨hc, hsp3⟩ := hsp2
        rcases cs' with _ | ⟨c', cs''⟩
        · rw [List.nil_append] at hsp3
          refine Or.inr (Or.inr (Or.inl ⟨bs, ?_, hA, hsp3.symm⟩))
          rw [hQ, hc]
        · rw [List.cons_append] at hsp3
          simp only [List.cons.injEq] at hsp3
          obtain ⟨hc', hsp4⟩ := hsp3
          refine Or.inr (Or.inr (Or.inr (Or.inr ⟨bs, cs'', ?_, hA, hsp4⟩)))
          rw [hQ, hc, hc']

/-! ## A relator occurrence is reduced -/

/-- An occurrence of a prefix of a symmetrized relator never contains a letter
beside its inverse: the relator is cyclically reduced, hence reduced, and being
reduced passes to contiguous subwords. -/
theorem not_cancel_in_relator [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) {r u v e f : List (α × Bool)}
    {x : α × Bool} (hr : r ∈ symmetrization R) (hsplit : r = u ++ v)
    (hu : u = e ++ (x :: invLetter x :: f)) : False := by
  have hred : FreeGroup.IsReduced r :=
    (symmetrization_isCyclicallyReduced hR hr).isReduced
  have hinf : u <:+: r := ⟨[], v, by rw [hsplit, List.nil_append]⟩
  have hu' : FreeGroup.IsReduced u := isReduced_of_infix hinf hred
  rw [hu] at hu'
  exact not_isReduced_cancel hu'

/-! ## One cancellation -/

/-- **Deleting one cancelling pair preserves reducibility**, given both closure
statements at strictly shorter words.  This is the whole free half of the
critical-pair analysis. -/
theorem dehnReducible_delete_pair [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) {n : ℕ}
    (hfree : FreeClosedBelow R n) (hswap : SwapClosedBelow R n)
    (A B : List (α × Bool)) (x : α × Bool)
    (hlen : (A ++ (x :: invLetter x :: B)).length ≤ n)
    (hW : DehnReducible R (A ++ (x :: invLetter x :: B))) :
    DehnReducible R (A ++ B) := by
  rcases Relation.ReflTransGen.cases_head hW with hnil | ⟨W₁, hstep, hW₁⟩
  · exfalso
    have hl := congrArg List.length hnil
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  · have hltW₁ : W₁.length < n := by
      have h1 := hstep.length_lt
      omega
    rcases dehnStep_iff.mp hstep with
      ⟨C, D, y, hWeq, hW₁eq⟩ | ⟨C, D, u, v, r, hr, hsplit, hlong, hWeq, hW₁eq⟩
    · -- a free first step: Mathlib's diamond lemma settles it outright
      have hstepR : FreeGroup.Red.Step (A ++ (x :: invLetter x :: B)) W₁ := by
        rw [hWeq, hW₁eq]
        exact redStep_of_pair C D y
      have hpairR : FreeGroup.Red.Step (A ++ (x :: invLetter x :: B)) (A ++ B) :=
        redStep_of_pair A B x
      rcases FreeGroup.Red.Step.diamond hstepR hpairR rfl with heq | ⟨Z, hZ1, hZ2⟩
      · rw [← heq]
        exact hW₁
      · have hZred : DehnReducible R Z := hfree W₁ hltW₁ hW₁ Z hZ1.to_red
        exact Relation.ReflTransGen.head (dehnStep_of_redStep hZ2) hZred
    · -- a Dehn first step: five configurations
      have hune : u ≠ [] := by
        intro hnil
        rw [hnil, List.length_nil] at hlong
        omega
      rcases pair_occurrence_cases hune hWeq with
        ⟨e, hC, hB⟩ | ⟨e, hA, hD⟩ | ⟨e, hQ, hA, hD⟩ | ⟨e, hQ, hC, hB⟩ |
          ⟨e, f, hQ, hA, hB⟩
      · -- disjoint, the step to the right of the pair
        have hshape : W₁
            = A ++ (x :: invLetter x :: (e ++ (FreeGroup.invRev v ++ D))) := by
          rw [hW₁eq, hC]
          simp only [List.append_assoc, List.cons_append]
        have hred₁ : DehnReducible R (A ++ (e ++ (FreeGroup.invRev v ++ D))) := by
          refine hfree W₁ hltW₁ hW₁ _ ?_
          rw [hshape]
          exact (redStep_of_pair A (e ++ (FreeGroup.invRev v ++ D)) x).to_red
        have hstep₂ : DehnStep R (A ++ (e ++ (u ++ D)))
            (A ++ (e ++ (FreeGroup.invRev v ++ D))) := by
          have hb := DehnStep.dehn (A ++ e) D u v r hr hsplit hlong
          simpa only [List.append_assoc] using hb
        rw [hB]
        exact Relation.ReflTransGen.head hstep₂ hred₁
      · -- disjoint, the step to the left of the pair
        have hshape : W₁
            = (C ++ (FreeGroup.invRev v ++ e)) ++ (x :: invLetter x :: B) := by
          rw [hW₁eq, hD]
          simp only [List.append_assoc]
        have hred₁ : DehnReducible R ((C ++ (FreeGroup.invRev v ++ e)) ++ B) := by
          refine hfree W₁ hltW₁ hW₁ _ ?_
          rw [hshape]
          exact (redStep_of_pair (C ++ (FreeGroup.invRev v ++ e)) B x).to_red
        have hstep₂ : DehnStep R ((C ++ (u ++ e)) ++ B)
            ((C ++ (FreeGroup.invRev v ++ e)) ++ B) := by
          have hb := DehnStep.dehn C (e ++ B) u v r hr hsplit hlong
          simpa only [List.append_assoc] using hb
        rw [hA]
        exact Relation.ReflTransGen.head hstep₂ hred₁
      · -- the step's occurrence ends at the pair's first letter
        have hmem : (e ++ [x]) ++ v ∈ symmetrization R := by
          rw [← hQ, ← hsplit]
          exact hr
        have hswapd : DehnSwap R (C ++ (e ++ B))
            (C ++ (FreeGroup.invRev v ++ (invLetter x :: B))) :=
          dehnSwap_of_straddle_right hmem
        have hshape : W₁ = C ++ (FreeGroup.invRev v ++ (invLetter x :: B)) := by
          rw [hW₁eq, hD]
        have hgoal : DehnReducible R (C ++ (e ++ B)) := by
          refine hswap _ ?_ ?_ _ hswapd.symm
          · rw [← hshape]
            exact hltW₁
          · rw [← hshape]
            exact hW₁
        rw [hA, List.append_assoc]
        exact hgoal
      · -- the step's occurrence begins at the pair's second letter
        have hmem : (invLetter x :: e) ++ v ∈ symmetrization R := by
          rw [← hQ, ← hsplit]
          exact hr
        have hswapd : DehnSwap R (A ++ (e ++ D))
            (A ++ (invLetter (invLetter x) :: (FreeGroup.invRev v ++ D))) :=
          dehnSwap_of_straddle_left hmem
        rw [invLetter_invLetter] at hswapd
        have hshape : W₁ = A ++ (x :: (FreeGroup.invRev v ++ D)) := by
          rw [hW₁eq, hC]
          simp only [List.append_assoc, List.singleton_append]
        have hgoal : DehnReducible R (A ++ (e ++ D)) := by
          refine hswap _ ?_ ?_ _ hswapd.symm
          · rw [← hshape]
            exact hltW₁
          · rw [← hshape]
            exact hW₁
        rw [hB]
        exact hgoal
      · -- the step's occurrence covers the pair, which it cannot
        exact (not_cancel_in_relator hR hr hsplit hQ).elim

/-! ## The stage passes to the next -/

/-- **Free closure at one more letter.**  A free reduction is a chain of
deletions; each is discharged by `dehnReducible_delete_pair`, and the word only
gets shorter along the chain. -/
theorem freeClosedBelow_succ [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) {n : ℕ}
    (hfree : FreeClosedBelow R n) (hswap : SwapClosedBelow R n) :
    FreeClosedBelow R (n + 1) := by
  intro W hlen hW G hred
  have hred' : Relation.ReflTransGen FreeGroup.Red.Step W G := hred
  clear hred
  induction hred' with
  | refl => exact hW
  | tail hab hbc ih =>
      cases hbc with
      | @not L₁ L₂ z zb =>
          have hlenb : (L₁ ++ ((z, zb) :: (z, !zb) :: L₂)).length ≤ n := by
            have hb := FreeGroup.Red.length_le hab
            omega
          exact dehnReducible_delete_pair hR hfree hswap L₁ L₂ (z, zb) hlenb ih

/-! ## The gate, from swap closure -/

/-- Free closure at every stage, from full swap closure. -/
theorem forall_freeClosedBelow [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hswap : DehnSwapClosed R) :
    ∀ n, FreeClosedBelow R n := by
  intro n
  induction n with
  | zero =>
      intro W hlen _ _ _
      exact absurd hlen (by omega)
  | succ n ih =>
      exact freeClosedBelow_succ hR ih (swapClosedBelow_of_dehnSwapClosed hswap n)

/-- **Free-reduction closure, from swap closure.** -/
theorem dehnFreeClosed_of_dehnSwapClosed [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hswap : DehnSwapClosed R) :
    DehnFreeClosed R :=
  dehnFreeClosed_of_below (forall_freeClosedBelow hR hswap)

/-- **The gate, from swap closure alone.**  A family of cyclically reduced
relators whose reducible words are closed under relator swaps satisfies the
Greendlinger conclusion. -/
theorem greendlingerConclusion_of_dehnSwapClosed [DecidableEq α]
    {R : Set (List (α × Bool))} (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hRne : ∀ r ∈ R, r ≠ []) (hswap : DehnSwapClosed R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_dehnFreeClosed hRne
    (dehnFreeClosed_of_dehnSwapClosed hR hswap)

end SmallCancellationRouter
end GroupApproximation
