import GroupApproximation.Sofic.GreendlingerDehnFree

/-!
# Relator swaps, discharged down to one overlap

`GreendlingerDehnFree` reduces the gate to swap closure: reducible words are
closed under replacing an occurrence of `u` by `invRev v`, for a split
`r = u ++ v` of a symmetrized relator.  This file runs the critical-pair analysis
for that statement and closes every configuration but one.

  `swapClosedBelow_succ` --- one stage of the joint induction
  `greendlingerConclusion_of_pieceOverlap` --- the gate, from the residual alone

## The analysis

The swap and the first step of a derivation are two occurrences in one word, and
`occurrence_cases` enumerates how they can sit: one strictly right of the other,
strictly left, one inside the other either way, or overlapping at either end.
Before any of that, two reductions:

* a swap that *lengthens* is free (`dehnReducible_of_swap_of_lt`), so only
  `|v| ≤ |u|` is left --- and this is what makes the piece bound bite, because it
  says `u` is at least half of its relator;
* a swap with `u = []` then has `v = []` and changes nothing.

The configurations, for a Dehn first step:

* **disjoint** (either side) --- the step and the swap commute.  Swap closure at
  the step's output, which is shorter, then replay the step.
* **step inside the swap's block** --- `C'(1/6)` forces the two relators to be one
  and the same rotated (`eq_rotate_of_occurrence`: an occurrence more than half of
  its own relator cannot be a piece), and then the step's output *freely* reduces
  to the swap's output (`red_of_inner_step`).  Free closure at the step's output.
* **swap's block inside the step** --- the same forcing, run the other way round,
  and this one closes outright (`dehnReducible_of_outer_step`).
* **overlapping**, either end --- here the two relators may genuinely be distinct,
  and the overlap `σ` is then a piece.  If they are *not* distinct the two outputs
  free-reduce to one and the same word and free closure joins them.  If they are,
  everything turns on how much of the step's occurrence lies beyond the overlap:
  when that part is more than half of the step's relator it carries a Dehn step of
  its own, and the swapped word steps onto the swap of the step's output
  (`dehnStep_of_middle_occurrence`, `dehnSwap_of_middle_step`, and their mirrors).

What is left is exactly the complementary regime: two distinct relators
overlapping in a piece, with the part beyond the overlap at most half.  The two
ends of the overlap are mirror images (`pieceOverlapLeft_of_right`), so the gate
rests on the single statement `PieceOverlapRight`.  Everything else in it is now
a theorem.

## The induction

Free closure and swap closure are proved together by induction on word length
(`forall_closedBelow`), because each is used in the proof of the other and every
step of the system strictly shortens its word.  `greendlingerConclusion_of_‐
pieceOverlap` puts the two halves together and produces the Greendlinger
conclusion from the residual alone.

Unconditional except for the cyclically-reduced hypothesis, `C'(1/6)`, and the
two named residual statements.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Two occurrences in one word -/

/-- **The six configurations of two occurrences.**  Given one word carrying `u`
at position `|A|` and `p` at position `|C|`, either the two are disjoint (either
order), or one contains the other (either way), or they overlap in a nonempty
`σ` (at either end).

Proved from `List.append_eq_append_iff` alone, and stated over an arbitrary
alphabet: nothing in it is about free groups. -/
theorem occurrence_cases {β : Type*} {A B C D u p : List β}
    (h : A ++ (u ++ B) = C ++ (p ++ D)) :
    (∃ e, C = A ++ (u ++ e) ∧ B = e ++ (p ++ D))
      ∨ (∃ e, A = C ++ (p ++ e) ∧ D = e ++ (u ++ B))
      ∨ (∃ a b, u = a ++ (p ++ b) ∧ C = A ++ a ∧ D = b ++ B)
      ∨ (∃ a b, p = a ++ (u ++ b) ∧ A = C ++ a ∧ B = b ++ D)
      ∨ (∃ γ σ τ, σ ≠ [] ∧ u = γ ++ σ ∧ p = σ ++ τ ∧ C = A ++ γ ∧ B = τ ++ D)
      ∨ (∃ γ σ τ, σ ≠ [] ∧ p = γ ++ σ ∧ u = σ ++ τ ∧ A = C ++ γ ∧ D = τ ++ B) := by
  rcases List.append_eq_append_iff.mp h with ⟨as, hC, hsp⟩ | ⟨bs, hA, hsp⟩
  · -- `C = A ++ as`, so `p` starts at or after `u`
    rcases List.append_eq_append_iff.mp hsp with ⟨cs, has, hB⟩ | ⟨ds, hu, hpD⟩
    · exact Or.inl ⟨cs, by rw [hC, has], hB⟩
    · rcases List.append_eq_append_iff.mp hpD with ⟨es, hds, hD⟩ | ⟨fs, hp, hB⟩
      · exact Or.inr (Or.inr (Or.inl ⟨as, es, by rw [hu, hds], hC, hD⟩))
      · rcases ds with _ | ⟨d, ds'⟩
        · -- nothing of `p` lies inside `u`
          refine Or.inl ⟨[], ?_, ?_⟩
          · simp [hC, hu]
          · simp [hB, hp]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨as, d :: ds', fs, List.cons_ne_nil _ _, hu, hp, hC, hB⟩))))
  · -- `A = C ++ bs`, so `p` starts at or before `u`
    rcases List.append_eq_append_iff.mp hsp with ⟨cs, hbs, hD⟩ | ⟨ds, hp, huB⟩
    · exact Or.inr (Or.inl ⟨cs, by rw [hA, hbs], hD⟩)
    · rcases List.append_eq_append_iff.mp huB with ⟨es, hds, hB⟩ | ⟨fs, hu, hD⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨bs, es, by rw [hp, hds], hA, hB⟩)))
      · rcases ds with _ | ⟨d, ds'⟩
        · refine Or.inr (Or.inl ⟨[], ?_, ?_⟩)
          · simp [hA, hp]
          · simp [hD, hu]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨bs, d :: ds', fs, List.cons_ne_nil _ _, hp, hu, hA, hD⟩))))

/-! ## One swap -/

/-- **A swap preserves reducibility**, given both closure statements at strictly
shorter words and the two residual overlaps.  This is the whole swap half of the
critical-pair analysis. -/
theorem dehnReducible_swap [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hpr : PieceOverlapRight R) (hpl : PieceOverlapLeft R) {n : ℕ}
    (hfree : FreeClosedBelow R n) (hswap : SwapClosedBelow R n)
    {A B u v r : List (α × Bool)} (hr : r ∈ symmetrization R) (hsplit : r = u ++ v)
    (hlen : (A ++ (u ++ B)).length ≤ n)
    (hW : DehnReducible R (A ++ (u ++ B))) :
    DehnReducible R (A ++ (FreeGroup.invRev v ++ B)) := by
  by_cases hle : v.length ≤ u.length
  swap
  · exact dehnReducible_of_swap_of_lt hr hsplit (by omega) hW
  rcases eq_or_ne u [] with rfl | hune
  · have hvlen : v.length = 0 := by
      rw [List.length_nil] at hle
      omega
    have hv : v = [] := List.length_eq_zero_iff.mp hvlen
    rw [hv, invRev_nil]
    exact hW
  rcases Relation.ReflTransGen.cases_head hW with hnil | ⟨W₁, hstep, hW₁⟩
  · exfalso
    have hl := congrArg List.length hnil
    simp only [List.length_append, List.length_nil] at hl
    exact hune (List.length_eq_zero_iff.mp (by omega))
  have hltW₁ : W₁.length < n := by
    have h1 := hstep.length_lt
    omega
  rcases dehnStep_iff.mp hstep with
    ⟨C, D, y, hWeq, hW₁eq⟩ | ⟨C, D, u₂, v₂, r₂, hr₂, hsplit₂, hlong₂, hWeq, hW₁eq⟩
  · -- ## a free first step
    have hWeq' : C ++ (y :: invLetter y :: D) = A ++ (u ++ B) := hWeq.symm
    rcases pair_occurrence_cases hune hWeq' with
      ⟨e, hA, hD⟩ | ⟨e, hC, hB⟩ | ⟨e, hu, hC, hB⟩ | ⟨e, hu, hA, hD⟩ | ⟨e, f, hu, hC, hD⟩
    · -- the pair lies strictly left of the swap's block
      have hW₁shape : W₁ = (C ++ e) ++ (u ++ B) := by
        rw [hW₁eq, hD]
        simp only [List.append_assoc]
      have hsw₁ : DehnSwap R ((C ++ e) ++ (u ++ B))
          ((C ++ e) ++ (FreeGroup.invRev v ++ B)) :=
        ⟨C ++ e, B, u, v, r, hr, hsplit, rfl, rfl⟩
      have hred₁ : DehnReducible R ((C ++ e) ++ (FreeGroup.invRev v ++ B)) := by
        refine hswap _ ?_ ?_ _ hsw₁
        · rw [← hW₁shape]
          exact hltW₁
        · rw [← hW₁shape]
          exact hW₁
      have hstep₂ : DehnStep R (A ++ (FreeGroup.invRev v ++ B))
          ((C ++ e) ++ (FreeGroup.invRev v ++ B)) := by
        have hb : DehnStep R
            (C ++ (y :: invLetter y :: (e ++ (FreeGroup.invRev v ++ B))))
            (C ++ (e ++ (FreeGroup.invRev v ++ B))) := DehnStep.free C _ y
        rw [hA]
        simpa only [List.append_assoc, List.cons_append] using hb
      exact Relation.ReflTransGen.head hstep₂ hred₁
    · -- the pair lies strictly right of the swap's block
      have hW₁shape : W₁ = A ++ (u ++ (e ++ D)) := by
        rw [hW₁eq, hC]
        simp only [List.append_assoc]
      have hsw₁ : DehnSwap R (A ++ (u ++ (e ++ D)))
          (A ++ (FreeGroup.invRev v ++ (e ++ D))) :=
        ⟨A, e ++ D, u, v, r, hr, hsplit, rfl, rfl⟩
      have hred₁ : DehnReducible R (A ++ (FreeGroup.invRev v ++ (e ++ D))) := by
        refine hswap _ ?_ ?_ _ hsw₁
        · rw [← hW₁shape]
          exact hltW₁
        · rw [← hW₁shape]
          exact hW₁
      have hstep₂ : DehnStep R
          (A ++ (FreeGroup.invRev v ++ (e ++ (y :: invLetter y :: D))))
          (A ++ (FreeGroup.invRev v ++ (e ++ D))) := by
        have hb := DehnStep.free (R := R) (A ++ (FreeGroup.invRev v ++ e)) D y
        simpa only [List.append_assoc] using hb
      rw [hB]
      exact Relation.ReflTransGen.head hstep₂ hred₁
    · -- the swap's block ends at the pair's first letter
      have hmem : (e ++ [y]) ++ v ∈ symmetrization R := by
        rw [← hu, ← hsplit]
        exact hr
      have hW₁shape : W₁ = A ++ (e ++ D) := by
        rw [hW₁eq, hC]
        simp only [List.append_assoc]
      have hswapd : DehnSwap R (A ++ (e ++ D))
          (A ++ (FreeGroup.invRev v ++ (invLetter y :: D))) :=
        dehnSwap_of_straddle_right hmem
      rw [hB]
      refine hswap _ ?_ ?_ _ hswapd
      · rw [← hW₁shape]
        exact hltW₁
      · rw [← hW₁shape]
        exact hW₁
    · -- the swap's block begins at the pair's second letter
      have hmem : (invLetter y :: e) ++ v ∈ symmetrization R := by
        rw [← hu, ← hsplit]
        exact hr
      have hswapd : DehnSwap R (C ++ (e ++ B))
          (C ++ (invLetter (invLetter y) :: (FreeGroup.invRev v ++ B))) :=
        dehnSwap_of_straddle_left hmem
      rw [invLetter_invLetter] at hswapd
      have hW₁shape : W₁ = C ++ (e ++ B) := by
        rw [hW₁eq, hD]
      have hgoal : DehnReducible R (C ++ (y :: (FreeGroup.invRev v ++ B))) := by
        refine hswap _ ?_ ?_ _ hswapd
        · rw [← hW₁shape]
          exact hltW₁
        · rw [← hW₁shape]
          exact hW₁
      rw [hA]
      simpa only [List.append_assoc, List.singleton_append] using hgoal
    · -- the swap's block covers the pair, which it cannot
      exact (not_cancel_in_relator hR hr hsplit hu).elim
  · -- ## a Dehn first step
    rcases occurrence_cases hWeq with
      ⟨e, hC, hB⟩ | ⟨e, hA, hD⟩ | ⟨a, b, hu, hC, hD⟩ | ⟨a, b, hu₂, hA, hB⟩ |
        ⟨γ, σ, τ, -, hu, hu₂, hC, hB⟩ | ⟨γ, σ, τ, -, hu₂, hu, hA, hD⟩
    · -- the step lies strictly right of the swap's block
      have hW₁shape : W₁ = A ++ (u ++ (e ++ (FreeGroup.invRev v₂ ++ D))) := by
        rw [hW₁eq, hC]
        simp only [List.append_assoc]
      have hsw₁ : DehnSwap R (A ++ (u ++ (e ++ (FreeGroup.invRev v₂ ++ D))))
          (A ++ (FreeGroup.invRev v ++ (e ++ (FreeGroup.invRev v₂ ++ D)))) :=
        ⟨A, e ++ (FreeGroup.invRev v₂ ++ D), u, v, r, hr, hsplit, rfl, rfl⟩
      have hred₁ : DehnReducible R
          (A ++ (FreeGroup.invRev v ++ (e ++ (FreeGroup.invRev v₂ ++ D)))) := by
        refine hswap _ ?_ ?_ _ hsw₁
        · rw [← hW₁shape]
          exact hltW₁
        · rw [← hW₁shape]
          exact hW₁
      have hstep₂ : DehnStep R (A ++ (FreeGroup.invRev v ++ (e ++ (u₂ ++ D))))
          (A ++ (FreeGroup.invRev v ++ (e ++ (FreeGroup.invRev v₂ ++ D)))) := by
        have hb := DehnStep.dehn (A ++ (FreeGroup.invRev v ++ e)) D u₂ v₂ r₂ hr₂
          hsplit₂ hlong₂
        simpa only [List.append_assoc] using hb
      rw [hB]
      exact Relation.ReflTransGen.head hstep₂ hred₁
    · -- the step lies strictly left of the swap's block
      have hW₁shape : W₁ = (C ++ (FreeGroup.invRev v₂ ++ e)) ++ (u ++ B) := by
        rw [hW₁eq, hD]
        simp only [List.append_assoc]
      have hsw₁ : DehnSwap R ((C ++ (FreeGroup.invRev v₂ ++ e)) ++ (u ++ B))
          ((C ++ (FreeGroup.invRev v₂ ++ e)) ++ (FreeGroup.invRev v ++ B)) :=
        ⟨C ++ (FreeGroup.invRev v₂ ++ e), B, u, v, r, hr, hsplit, rfl, rfl⟩
      have hred₁ : DehnReducible R
          ((C ++ (FreeGroup.invRev v₂ ++ e)) ++ (FreeGroup.invRev v ++ B)) := by
        refine hswap _ ?_ ?_ _ hsw₁
        · rw [← hW₁shape]
          exact hltW₁
        · rw [← hW₁shape]
          exact hW₁
      have hstep₂ : DehnStep R ((C ++ (u₂ ++ e)) ++ (FreeGroup.invRev v ++ B))
          ((C ++ (FreeGroup.invRev v₂ ++ e)) ++ (FreeGroup.invRev v ++ B)) := by
        have hb := DehnStep.dehn C (e ++ (FreeGroup.invRev v ++ B)) u₂ v₂ r₂ hr₂
          hsplit₂ hlong₂
        simpa only [List.append_assoc] using hb
      rw [hA]
      exact Relation.ReflTransGen.head hstep₂ hred₁
    · -- the step is buried inside the swap's block
      have hsplit' : r = (a ++ (u₂ ++ b)) ++ v := by rw [hsplit, hu]
      have hredc := red_of_inner_step (A := A) (B := B) hmetric hr hr₂ hsplit'
        hsplit₂ hlong₂
      have hW₁shape : W₁ = (A ++ a) ++ (FreeGroup.invRev v₂ ++ (b ++ B)) := by
        rw [hW₁eq, hC, hD]
      refine hfree W₁ hltW₁ hW₁ _ ?_
      rw [hW₁shape]
      exact hredc
    · -- the swap's block is buried inside the step
      have hsplit₂' : r₂ = (a ++ (u ++ b)) ++ v₂ := by rw [hsplit₂, hu₂]
      have hW₁' : DehnReducible R (C ++ (FreeGroup.invRev v₂ ++ D)) := by
        rw [← hW₁eq]
        exact hW₁
      have hgoal := dehnReducible_of_outer_step hmetric hr hr₂ hsplit hsplit₂' hle hW₁'
      rw [hA, hB]
      exact hgoal
    · -- ## the step overlaps the swap's block on the right
      have hrocc : r = γ ++ (σ ++ v) := by
        rw [hsplit, hu, List.append_assoc]
      have hr₂occ : r₂ = σ ++ (τ ++ v₂) := by
        rw [hsplit₂, hu₂, List.append_assoc]
      have hpre : σ <+: r₂ := ⟨τ ++ v₂, hr₂occ.symm⟩
      have hW₁shape : W₁ = (A ++ γ) ++ (FreeGroup.invRev v₂ ++ D) := by
        rw [hW₁eq, hC]
      by_cases hsame : r₂ = r.rotate γ.length
      · -- one and the same relator: the two outputs meet after free reduction
        have hcomp : τ ++ v₂ = v ++ γ := tail_eq_of_eq_rotate hrocc hsame hr₂occ
        rcases List.append_eq_append_iff.mp hcomp with ⟨w, hv, hv₂⟩ | ⟨w, hτ, hγ⟩
        · have hGZ : FreeGroup.Red (A ++ (FreeGroup.invRev v ++ B))
              (A ++ (FreeGroup.invRev w ++ D)) := by
            have hb := red_cancel_block' τ (A ++ FreeGroup.invRev w) D
            have hshape : A ++ (FreeGroup.invRev v ++ B)
                = (A ++ FreeGroup.invRev w) ++ (FreeGroup.invRev τ ++ τ) ++ D := by
              rw [hv, hB, FreeGroup.invRev_append]
              simp only [List.append_assoc]
            have hshape2 : (A ++ FreeGroup.invRev w) ++ D
                = A ++ (FreeGroup.invRev w ++ D) := by
              simp only [List.append_assoc]
            rw [hshape, ← hshape2]
            exact hb
          have hWZ : FreeGroup.Red W₁ (A ++ (FreeGroup.invRev w ++ D)) := by
            have hb := red_cancel_block γ A (FreeGroup.invRev w ++ D)
            have hshape : W₁
                = A ++ (γ ++ FreeGroup.invRev γ) ++ (FreeGroup.invRev w ++ D) := by
              rw [hW₁shape, hv₂, FreeGroup.invRev_append]
              simp only [List.append_assoc]
            rw [hshape]
            exact hb
          exact (dehnRed_of_red hGZ).trans (hfree W₁ hltW₁ hW₁ _ hWZ)
        · have hGZ : FreeGroup.Red (A ++ (FreeGroup.invRev v ++ B))
              (A ++ (w ++ D)) := by
            have hb := red_cancel_block' v A (w ++ D)
            have hshape : A ++ (FreeGroup.invRev v ++ B)
                = A ++ (FreeGroup.invRev v ++ v) ++ (w ++ D) := by
              rw [hB, hτ]
              simp only [List.append_assoc]
            rw [hshape]
            exact hb
          have hWZ : FreeGroup.Red W₁ (A ++ (w ++ D)) := by
            have hb := red_cancel_block v₂ (A ++ w) D
            have hshape : W₁ = (A ++ w) ++ (v₂ ++ FreeGroup.invRev v₂) ++ D := by
              rw [hW₁shape, hγ]
              simp only [List.append_assoc]
            have hshape2 : (A ++ w) ++ D = A ++ (w ++ D) := by
              simp only [List.append_assoc]
            rw [hshape, ← hshape2]
            exact hb
          exact (dehnRed_of_red hGZ).trans (hfree W₁ hltW₁ hW₁ _ hWZ)
      · -- distinct relators: the overlap is a piece
        have hγσ : γ ++ σ <+: r := ⟨v, by rw [hrocc, List.append_assoc]⟩
        have hp2 : σ <+: r.rotate γ.length := prefix_rotate_of_append_prefix hγσ
        have hrot : r.rotate γ.length ∈ symmetrization R :=
          rotate_mem_symmetrization hr γ.length
        have hpiece : IsPiece (symmetrization R) σ :=
          isPiece_of_prefix_two hr₂ hrot hsame hpre hp2
        have h6 := six_mul_length_lt_of_isPiece hmetric hpiece hr₂ hpre
        have hmem₂ : σ ++ (τ ++ v₂) ∈ symmetrization R := by
          rw [← hr₂occ]
          exact hr₂
        have hmem : (γ ++ σ) ++ v ∈ symmetrization R := by
          rw [← hu, ← hsplit]
          exact hr
        rcases Nat.lt_or_ge ((σ ++ (τ ++ v₂)).length) (2 * τ.length) with hbig | hsmall
        · -- what the step keeps beyond the overlap carries a step of its own
          have hstepG := dehnStep_of_middle_occurrence hmem₂ hbig
            (A ++ FreeGroup.invRev v) D
          have hswapd : DehnSwap R ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ D))
              (A ++ (FreeGroup.invRev v ++ (FreeGroup.invRev (v₂ ++ σ) ++ D))) :=
            dehnSwap_of_middle_step hmem
          have hY : DehnReducible R
              (A ++ (FreeGroup.invRev v ++ (FreeGroup.invRev (v₂ ++ σ) ++ D))) := by
            refine hswap _ ?_ ?_ _ hswapd
            · rw [← hW₁shape]
              exact hltW₁
            · rw [← hW₁shape]
              exact hW₁
          have hstep₂ : DehnStep R (A ++ (FreeGroup.invRev v ++ (τ ++ D)))
              (A ++ (FreeGroup.invRev v ++ (FreeGroup.invRev (v₂ ++ σ) ++ D))) := by
            simpa only [List.append_assoc] using hstepG
          rw [hB]
          exact Relation.ReflTransGen.head hstep₂ hY
        · -- the residual overlap
          have hW₁' : DehnReducible R ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ D)) := by
            rw [← hW₁shape]
            exact hW₁
          have hlen' : v.length ≤ (γ ++ σ).length := by
            rw [← hu]
            exact hle
          have hv₂ : v₂.length < (σ ++ τ).length := by
            rw [← hu₂]
            rw [hsplit₂, List.length_append] at hlong₂
            omega
          have h6' : 6 * σ.length < ((σ ++ τ) ++ v₂).length := by
            rw [← hu₂, ← hsplit₂]
            exact h6
          have hsmall' : 2 * τ.length ≤ ((σ ++ τ) ++ v₂).length := by
            rw [← hu₂, ← hsplit₂, hr₂occ]
            exact hsmall
          rw [hB]
          exact hpr hmetric A γ σ τ v v₂ D hmem
            (by rw [← hu₂, ← hsplit₂]; exact hr₂) h6' hlen' hv₂ hsmall' hW₁'
    · -- ## the step overlaps the swap's block on the left
      have hrocc : r = σ ++ (τ ++ v) := by
        rw [hsplit, hu, List.append_assoc]
      have hr₂occ : r₂ = γ ++ (σ ++ v₂) := by
        rw [hsplit₂, hu₂, List.append_assoc]
      have hpre : σ <+: r := ⟨τ ++ v, hrocc.symm⟩
      have hW₁shape : W₁ = C ++ (FreeGroup.invRev v₂ ++ (τ ++ B)) := by
        rw [hW₁eq, hD]
      by_cases hsame : r = r₂.rotate γ.length
      · -- one and the same relator
        have hcomp : τ ++ v = v₂ ++ γ := tail_eq_of_eq_rotate hr₂occ hsame hrocc
        rcases List.append_eq_append_iff.mp hcomp with ⟨w, hv₂, hv⟩ | ⟨w, hτ, hγ⟩
        · have hGZ : FreeGroup.Red (A ++ (FreeGroup.invRev v ++ B))
              (C ++ (FreeGroup.invRev w ++ B)) := by
            have hb := red_cancel_block γ C (FreeGroup.invRev w ++ B)
            have hshape : A ++ (FreeGroup.invRev v ++ B)
                = C ++ (γ ++ FreeGroup.invRev γ) ++ (FreeGroup.invRev w ++ B) := by
              rw [hA, hv, FreeGroup.invRev_append]
              simp only [List.append_assoc]
            rw [hshape]
            exact hb
          have hWZ : FreeGroup.Red W₁ (C ++ (FreeGroup.invRev w ++ B)) := by
            have hb := red_cancel_block' τ (C ++ FreeGroup.invRev w) B
            have hshape : W₁
                = (C ++ FreeGroup.invRev w) ++ (FreeGroup.invRev τ ++ τ) ++ B := by
              rw [hW₁shape, hv₂, FreeGroup.invRev_append]
              simp only [List.append_assoc]
            have hshape2 : (C ++ FreeGroup.invRev w) ++ B
                = C ++ (FreeGroup.invRev w ++ B) := by
              simp only [List.append_assoc]
            rw [hshape, ← hshape2]
            exact hb
          exact (dehnRed_of_red hGZ).trans (hfree W₁ hltW₁ hW₁ _ hWZ)
        · have hGZ : FreeGroup.Red (A ++ (FreeGroup.invRev v ++ B))
              (C ++ (w ++ B)) := by
            have hb := red_cancel_block v (C ++ w) B
            have hshape : A ++ (FreeGroup.invRev v ++ B)
                = (C ++ w) ++ (v ++ FreeGroup.invRev v) ++ B := by
              rw [hA, hγ]
              simp only [List.append_assoc]
            have hshape2 : (C ++ w) ++ B = C ++ (w ++ B) := by
              simp only [List.append_assoc]
            rw [hshape, ← hshape2]
            exact hb
          have hWZ : FreeGroup.Red W₁ (C ++ (w ++ B)) := by
            have hb := red_cancel_block' v₂ C (w ++ B)
            have hshape : W₁ = C ++ (FreeGroup.invRev v₂ ++ v₂) ++ (w ++ B) := by
              rw [hW₁shape, hτ]
              simp only [List.append_assoc]
            rw [hshape]
            exact hb
          exact (dehnRed_of_red hGZ).trans (hfree W₁ hltW₁ hW₁ _ hWZ)
      · -- distinct relators: the overlap is a piece
        have hγσ : γ ++ σ <+: r₂ := ⟨v₂, by rw [hr₂occ, List.append_assoc]⟩
        have hp2 : σ <+: r₂.rotate γ.length := prefix_rotate_of_append_prefix hγσ
        have hrot : r₂.rotate γ.length ∈ symmetrization R :=
          rotate_mem_symmetrization hr₂ γ.length
        have hpiece : IsPiece (symmetrization R) σ :=
          isPiece_of_prefix_two hr hrot hsame hpre hp2
        have h6 := six_mul_length_lt_of_isPiece hmetric hpiece hrot hp2
        rw [List.length_rotate] at h6
        have hmem₂ : (γ ++ σ) ++ v₂ ∈ symmetrization R := by
          rw [← hu₂, ← hsplit₂]
          exact hr₂
        have hmem : (σ ++ τ) ++ v ∈ symmetrization R := by
          rw [← hu, ← hsplit]
          exact hr
        rcases Nat.lt_or_ge (((γ ++ σ) ++ v₂).length) (2 * γ.length) with hbig | hsmall
        · -- what the step keeps before the overlap carries a step of its own
          have hstepG := dehnStep_of_front_occurrence hmem₂ hbig C
            (FreeGroup.invRev v ++ B)
          have hswapd : DehnSwap R (C ++ (FreeGroup.invRev v₂ ++ (τ ++ B)))
              (C ++ (FreeGroup.invRev v₂ ++ (FreeGroup.invRev (v ++ σ) ++ B))) :=
            dehnSwap_of_front_step hmem
          have hY : DehnReducible R
              (C ++ (FreeGroup.invRev v₂ ++ (FreeGroup.invRev (v ++ σ) ++ B))) := by
            refine hswap _ ?_ ?_ _ hswapd
            · rw [← hW₁shape]
              exact hltW₁
            · rw [← hW₁shape]
              exact hW₁
          have hshapeY : C ++ (FreeGroup.invRev (σ ++ v₂) ++ (FreeGroup.invRev v ++ B))
              = C ++ (FreeGroup.invRev v₂ ++ (FreeGroup.invRev (v ++ σ) ++ B)) := by
            rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
            simp only [List.append_assoc]
          have hstep₂ : DehnStep R ((C ++ γ) ++ (FreeGroup.invRev v ++ B))
              (C ++ (FreeGroup.invRev v₂ ++ (FreeGroup.invRev (v ++ σ) ++ B))) := by
            rw [← hshapeY]
            simpa only [List.append_assoc] using hstepG
          rw [hA]
          exact Relation.ReflTransGen.head hstep₂ hY
        · -- the residual overlap, mirrored
          have hW₁' : DehnReducible R (C ++ (FreeGroup.invRev v₂ ++ (τ ++ B))) := by
            rw [← hW₁shape]
            exact hW₁
          have hlen' : v.length ≤ (σ ++ τ).length := by
            rw [← hu]
            exact hle
          have hv₂ : v₂.length < (γ ++ σ).length := by
            rw [← hu₂]
            rw [hsplit₂, List.length_append] at hlong₂
            omega
          have h6' : 6 * σ.length < ((γ ++ σ) ++ v₂).length := by
            rw [← hu₂, ← hsplit₂]
            exact h6
          rw [hA]
          exact hpl hmetric C γ σ τ v v₂ B hmem hmem₂ h6' hlen' hv₂ hsmall hW₁'

/-! ## The two closures, together -/

/-- **Swap closure at one more letter.** -/
theorem swapClosedBelow_succ [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hpr : PieceOverlapRight R) (hpl : PieceOverlapLeft R) {n : ℕ}
    (hfree : FreeClosedBelow R n) (hswap : SwapClosedBelow R n) :
    SwapClosedBelow R (n + 1) := by
  intro W hlen hW G hsw
  obtain ⟨A, B, u, v, r, hr, hsplit, hWeq, hGeq⟩ := hsw
  subst hGeq
  subst hWeq
  exact dehnReducible_swap hR hmetric hpr hpl hfree hswap hr hsplit (by omega) hW

/-- **Both closures, at every stage**, by induction on word length: each half
uses the other only at strictly shorter words. -/
theorem forall_closedBelow [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R (1 / 6)) (hpr : PieceOverlapRight R) :
    ∀ n, FreeClosedBelow R n ∧ SwapClosedBelow R n := by
  have hpl : PieceOverlapLeft R := pieceOverlapLeft_of_right hpr
  intro n
  induction n with
  | zero =>
      constructor
      · intro W hlen _ _ _
        exact absurd hlen (by omega)
      · intro W hlen _ _ _
        exact absurd hlen (by omega)
  | succ n ih =>
      exact ⟨freeClosedBelow_succ hR ih.1 ih.2,
        swapClosedBelow_succ hR hmetric hpr hpl ih.1 ih.2⟩

/-- **Free-reduction closure, from the residual overlaps alone.** -/
theorem dehnFreeClosed_of_pieceOverlap [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R (1 / 6)) (hpr : PieceOverlapRight R) :
    DehnFreeClosed R :=
  dehnFreeClosed_of_below fun n => (forall_closedBelow hR hmetric hpr n).1

/-- **Swap closure, from the residual overlaps alone.** -/
theorem dehnSwapClosed_of_pieceOverlap [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R (1 / 6)) (hpr : PieceOverlapRight R) :
    DehnSwapClosed R :=
  dehnSwapClosed_of_below fun n => (forall_closedBelow hR hmetric hpr n).2

/-- **The gate, from the residual overlaps alone.**  Every configuration of the
critical-pair analysis except the two mirror-image piece overlaps is discharged,
so a `C'(1/6)` family of cyclically reduced relators satisfying them satisfies the
Greendlinger conclusion. -/
theorem greendlingerConclusion_of_pieceOverlap [DecidableEq α]
    {R : Set (List (α × Bool))} (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    (hpr : PieceOverlapRight R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_dehnFreeClosed hRne
    (dehnFreeClosed_of_pieceOverlap hR hmetric hpr)

end SmallCancellationRouter
end GroupApproximation
