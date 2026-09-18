import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.Trail
import GroupApproximation.Meta.AxiomGuard

/-!
# Balanced lists and the count along a trail

A list `l` with start label `s` and end label `t` is *balanced* when, at every label `x`, as many
entries start at `x` as end at `x`.

* `IsBalanced.perm`: balance only depends on the multiset.
* `chain_countP`: along a nonempty trail (consecutive entries chain), at every label `x`,
  `#starts + [last ends at x] = #ends + [first starts at x]`.  Induction on the list: prepending
  `a` to a trail starting with `b` adds `[a starts at x]` and `[a ends at x] = [b starts at x]`.
* `IsClosedTrail.isBalanced`: a closed trail is balanced (the two correction terms agree).
* `IsBalanced.cancel_left`: if `A ++ B` and `A` are balanced, so is `B`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler

section Generic

variable {α V : Type*} {s t : α → V}

/-- **A balanced list.**  At every label, as many entries start there as end there. -/
def IsBalanced [DecidableEq V] (s t : α → V) (l : List α) : Prop :=
  ∀ x : V, l.countP (fun d => decide (s d = x)) = l.countP (fun d => decide (t d = x))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsBalanced

/-- Balance is invariant under permutations. -/
theorem IsBalanced.perm [DecidableEq V] {l l' : List α} (h : IsBalanced s t l)
    (hp : l.Perm l') : IsBalanced s t l' := by
  intro x
  exact (hp.countP_eq _).symm.trans ((h x).trans (hp.countP_eq _))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsBalanced.perm

/-- The count along a trail, for a list written as `a :: l`. -/
theorem chain_countP_cons [DecidableEq V] (x : V) :
    ∀ (a : α) (l : List α), (a :: l).IsChain (fun a b => t a = s b) →
      (a :: l).countP (fun d => decide (s d = x)) +
          [(a :: l).getLast (List.cons_ne_nil a l)].countP (fun d => decide (t d = x)) =
        (a :: l).countP (fun d => decide (t d = x)) + [a].countP (fun d => decide (s d = x)) := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _
    exact Nat.add_comm _ _
  | cons b l ih =>
    intro hchain
    obtain ⟨hab, hbl⟩ := List.isChain_cons_cons.mp hchain
    have hih := ih b hbl
    have hlast : (a :: b :: l).getLast (List.cons_ne_nil a (b :: l)) =
        (b :: l).getLast (List.cons_ne_nil b l) := rfl
    have e1 : (a :: b :: l).countP (fun d => decide (s d = x)) =
        [a].countP (fun d => decide (s d = x)) + (b :: l).countP (fun d => decide (s d = x)) :=
      List.countP_append (l₁ := [a]) (l₂ := b :: l)
    have e2 : (a :: b :: l).countP (fun d => decide (t d = x)) =
        [a].countP (fun d => decide (t d = x)) + (b :: l).countP (fun d => decide (t d = x)) :=
      List.countP_append (l₁ := [a]) (l₂ := b :: l)
    have hab' :
        [a].countP (fun d => decide (t d = x)) = [b].countP (fun d => decide (s d = x)) := by
      simp only [List.countP_singleton, hab]
    rw [e1, e2, hlast]
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.chain_countP_cons

/-- **The count along a trail.**  At every label `x`, the number of entries starting at `x` plus
`[the last entry ends at x]` equals the number of entries ending at `x` plus
`[the first entry starts at x]`. -/
theorem chain_countP [DecidableEq V] (x : V) {l : List α} (hne : l ≠ [])
    (hl : l.IsChain (fun a b => t a = s b)) :
    l.countP (fun d => decide (s d = x)) + [l.getLast hne].countP (fun d => decide (t d = x)) =
      l.countP (fun d => decide (t d = x)) + [l.head hne].countP (fun d => decide (s d = x)) := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact chain_countP_cons (s := s) (t := t) x a rest hl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.chain_countP

/-- **A closed trail is balanced.** -/
theorem IsClosedTrail.isBalanced [DecidableEq V] {l : List α} (h : IsClosedTrail s t l) :
    IsBalanced s t l := by
  intro x
  obtain ⟨hne, hchain, hclose⟩ := h
  have hc := chain_countP (s := s) (t := t) x hne hchain
  have he : [l.getLast hne].countP (fun d => decide (t d = x)) =
      [l.head hne].countP (fun d => decide (s d = x)) := by
    simp only [List.countP_singleton, hclose]
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.isBalanced

/-- **Removing a balanced block keeps a list balanced.** -/
theorem IsBalanced.cancel_left [DecidableEq V] {A B : List α} (hAB : IsBalanced s t (A ++ B))
    (hA : IsBalanced s t A) : IsBalanced s t B := by
  intro x
  have h1 := hAB x
  have h2 := hA x
  simp only [List.countP_append] at h1
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsBalanced.cancel_left

end Generic

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler
