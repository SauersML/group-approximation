import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.Balance
import GroupApproximation.Meta.AxiomGuard

/-!
# Extracting a closed trail from a balanced list

A balanced list contains, through any given entry `b`, a closed trail starting with `b`.

* `exists_closedTrail_extend`: walk forward.  Let `T` be a trail and `R` the entries not used yet,
  with `T ++ R` balanced.  If `T` is closed, stop.  Otherwise `T` ends at `w`, which is not where
  `T` starts, so by `chain_countP` at `w` the trail `T` has one start fewer than ends at `w`; by
  balance `R` has one start more than ends at `w`, so some entry `e` of `R` starts at `w`.  Append
  `e` to `T` and recurse on the shorter remainder (strong induction on `R.length`).
* `exists_closedTrail_head`: start the walk with `T = [b]`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler

section Generic

variable {α V : Type*} {s t : α → V}

/-- **Walking forward in a balanced list until the trail closes.** -/
theorem exists_closedTrail_extend [DecidableEq V] :
    ∀ (n : ℕ) (T R : List α) (hT : T ≠ []), R.length = n →
      T.IsChain (fun a b => t a = s b) → IsBalanced s t (T ++ R) →
      ∃ C R' : List α, ∃ hC : C ≠ [],
        IsClosedTrail s t C ∧ C.head hC = T.head hT ∧ (C ++ R').Perm (T ++ R) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T R hT hlen hchain hbal
    by_cases hclose : t (T.getLast hT) = s (T.head hT)
    · exact ⟨T, R, hT, ⟨hT, hchain, hclose⟩, rfl, List.Perm.refl _⟩
    · have hcount := chain_countP (s := s) (t := t) (t (T.getLast hT)) hT hchain
      have h1 : [T.getLast hT].countP (fun d => decide (t d = t (T.getLast hT))) = 1 := by
        simp
      have hne' : s (T.head hT) ≠ t (T.getLast hT) := fun h => hclose h.symm
      have h0 : [T.head hT].countP (fun d => decide (s d = t (T.getLast hT))) = 0 := by
        simp [hne']
      have hb := hbal (t (T.getLast hT))
      simp only [List.countP_append] at hb
      have hpos : 0 < R.countP (fun d => decide (s d = t (T.getLast hT))) := by
        omega
      obtain ⟨e, he, hse⟩ := List.countP_pos_iff.mp hpos
      have hse' : s e = t (T.getLast hT) := of_decide_eq_true hse
      obtain ⟨P, Q, rfl⟩ := List.append_of_mem he
      have hchain' : (T ++ [e]).IsChain (fun a b => t a = s b) := by
        refine List.IsChain.append hchain (List.isChain_singleton e) ?_
        intro x hx y hy
        simp only [List.getLast?_eq_some_getLast hT, Option.mem_def, Option.some.injEq] at hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hx hy
        exact hse'.symm
      have hperm : (T ++ [e] ++ (P ++ Q)).Perm (T ++ (P ++ e :: Q)) := by
        rw [List.append_assoc, List.singleton_append]
        exact List.Perm.append_left T List.perm_middle.symm
      have hT' : T ++ [e] ≠ [] := fun h => hT (List.append_eq_nil_iff.mp h).1
      have hlen' : (P ++ Q).length < n := by
        have h2 : (P ++ Q).length = P.length + Q.length := List.length_append
        have h3 : (P ++ e :: Q).length = P.length + (Q.length + 1) := by
          rw [List.length_append, List.length_cons]
        omega
      obtain ⟨C, R', hC, hCc, hhead, hCperm⟩ :=
        ih (P ++ Q).length hlen' (T ++ [e]) (P ++ Q) hT' rfl hchain' (hbal.perm hperm.symm)
      exact ⟨C, R', hC, hCc, hhead.trans (List.head_append_of_ne_nil hT), hCperm.trans hperm⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.exists_closedTrail_extend

/-- **A closed trail through a given entry of a balanced list.**  If `R` is balanced and `b ∈ R`,
some closed trail `C` starting with `b` and some list `R'` have `C ++ R'` a permutation of `R`. -/
theorem exists_closedTrail_head [DecidableEq V] {R : List α} (hbal : IsBalanced s t R) {b : α}
    (hb : b ∈ R) :
    ∃ C R' : List α, ∃ hC : C ≠ [],
      IsClosedTrail s t C ∧ C.head hC = b ∧ (C ++ R').Perm R := by
  obtain ⟨P, Q, rfl⟩ := List.append_of_mem hb
  have hperm : ([b] ++ (P ++ Q)).Perm (P ++ b :: Q) := by
    rw [List.singleton_append]
    exact List.perm_middle.symm
  obtain ⟨C, R', hC, hCc, hhead, hCperm⟩ :=
    exists_closedTrail_extend (s := s) (t := t) (P ++ Q).length [b] (P ++ Q)
      (List.cons_ne_nil b []) rfl (List.isChain_singleton b) (hbal.perm hperm.symm)
  exact ⟨C, R', hC, hCc, hhead, hCperm.trans hperm⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.exists_closedTrail_head

end Generic

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler
