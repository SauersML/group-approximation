import GroupApproximation.Dynamics.SubshiftWordGraph
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Cyclic edges give periodic models

An edge `w` of the word graph of `X` at level `r` is cyclic when a directed path leads from its
suffix back to its prefix.  Reading the letters around the resulting cycle gives a periodic word
`p : ZMod k → A` that starts with `w` and all of whose windows of length `r + 1` are words of `X`
(sec:chain-core, proof of lem:chain-core-models).  The periodic word need not belong to `X`; only
its windows are asked to.

* `exists_edgeWalk_of_reflTransGen`: an edge followed by a directed path is a sequence of edges of
  `X`, each suffix being the next prefix;
* `edge_apply_eq_of_tail_eq_init`: a cyclic sequence of overlapping edges is read from its first
  letters;
* `exists_periodic_of_isCyclicEdge`: a cyclic edge gives a periodic model with allowed windows.
-/

namespace GroupApproximation
namespace WordGraph

variable {A : Type*}

/-- An edge `w` of `X` with suffix `u`, followed by a directed path from `u` to `v` in the word
graph at level `r`, is a sequence `e 0 = w, …, e m` of edges of `X`, each suffix being the next
prefix, whose last suffix is `v`. -/
theorem exists_edgeWalk_of_reflTransGen {X : Set (ℤ → A)} {r : ℕ} {u v : Fin r → A}
    (h : Relation.ReflTransGen (wordEdge X r) u v) {w : Fin (r + 1) → A}
    (hw : w ∈ language X (r + 1)) (hwu : Fin.tail w = u) :
    ∃ (m : ℕ) (e : ℕ → Fin (r + 1) → A), e 0 = w ∧ (∀ i ≤ m, e i ∈ language X (r + 1)) ∧
      (∀ i < m, Fin.tail (e i) = Fin.init (e (i + 1))) ∧ Fin.tail (e m) = v := by
  induction h with
  | refl => exact ⟨0, fun _ => w, rfl, fun _ _ => hw, fun _ hi => by omega, hwu⟩
  | tail _ hbc ih =>
    obtain ⟨m, e, he0, heL, hcons, hem⟩ := ih
    obtain ⟨w', hw'L, hw'b, hw'c⟩ := hbc
    refine ⟨m + 1, fun i => if i ≤ m then e i else w', ?_, fun i _ => ?_, fun i hi => ?_, ?_⟩
    · show (if 0 ≤ m then e 0 else w') = w
      rw [if_pos (Nat.zero_le m), he0]
    · show (if i ≤ m then e i else w') ∈ language X (r + 1)
      by_cases him : i ≤ m
      · rw [if_pos him]
        exact heL i him
      · rw [if_neg him]
        exact hw'L
    · show Fin.tail (if i ≤ m then e i else w') = Fin.init (if i + 1 ≤ m then e (i + 1) else w')
      by_cases him : i < m
      · rw [if_pos (show i ≤ m by omega), if_pos (show i + 1 ≤ m by omega)]
        exact hcons i him
      · rw [show i = m by omega, if_pos (le_refl m), if_neg (show ¬m + 1 ≤ m by omega), hem, hw'b]
    · show Fin.tail (if m + 1 ≤ m then e (m + 1) else w') = _
      rw [if_neg (show ¬m + 1 ≤ m by omega)]
      exact hw'c

/-- In a cyclic sequence `E : ZMod k → Fin (r + 1) → A` of edges in which each suffix is the next
prefix, the edge at `n` is read from the first letters at `n, n + 1, …, n + r`. -/
theorem edge_apply_eq_of_tail_eq_init {k r : ℕ} (E : ZMod k → Fin (r + 1) → A)
    (hE : ∀ n, Fin.tail (E n) = Fin.init (E (n + 1))) (n : ZMod k) (j : Fin (r + 1)) :
    E (n + (j : ℕ)) ⟨0, by omega⟩ = E n j := by
  have key : ∀ (i : ℕ) (hi : i < r + 1) (n : ZMod k),
      E (n + (i : ℕ)) ⟨0, by omega⟩ = E n ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi n
      rw [Nat.cast_zero, add_zero]
    | succ i ih =>
      intro hi n
      have hir : i < r := by omega
      rw [show n + ((i + 1 : ℕ) : ZMod k) = n + 1 + (i : ℕ) by push_cast; ring, ih (by omega)]
      exact congrFun (hE n).symm ⟨i, hir⟩
  exact key j.1 j.2 n

/-- **A cyclic edge gives a periodic model.**  If the edge `w` of the word graph of `X` at level `r`
is cyclic, there is a periodic word `p : ZMod k → A` beginning with `w` all of whose windows of
length `r + 1` are words of `X`. -/
theorem exists_periodic_of_isCyclicEdge {X : Set (ℤ → A)} {r : ℕ} {w : Fin (r + 1) → A}
    (hw : IsCyclicEdge X r w) :
    ∃ (k : ℕ) (_ : NeZero k) (p : ZMod k → A), (∀ j : Fin (r + 1), p ((j : ℕ) : ZMod k) = w j) ∧
      ∀ n : ZMod k, (fun j : Fin (r + 1) => p (n + (j : ℕ))) ∈ language X (r + 1) := by
  obtain ⟨hwL, hpath⟩ := hw
  obtain ⟨m, e, he0, heL, hcons, hem⟩ := exists_edgeWalk_of_reflTransGen hpath hwL rfl
  have hE : ∀ n : ZMod (m + 1), Fin.tail (e n.val) = Fin.init (e (n + 1).val) := by
    intro n
    have hn := ZMod.val_lt n
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rcases Nat.lt_or_ge n.val m with h | h
    · rw [Nat.mod_eq_of_lt (show n.val + 1 < m + 1 by omega)]
      exact hcons n.val h
    · rw [show n.val = m by omega, Nat.mod_self, hem, he0]
  refine ⟨m + 1, inferInstance, fun n => e n.val ⟨0, by omega⟩, fun j => ?_, fun n => ?_⟩
  · have h := edge_apply_eq_of_tail_eq_init (fun n : ZMod (m + 1) => e n.val) hE 0 j
    simp only [zero_add, ZMod.val_zero, he0] at h
    exact h
  · have h : (fun j : Fin (r + 1) => e (n + ((j : ℕ) : ZMod (m + 1))).val ⟨0, by omega⟩) =
        e n.val :=
      funext fun j => edge_apply_eq_of_tail_eq_init (fun n : ZMod (m + 1) => e n.val) hE n j
    obtain ⟨x, hx, hxw⟩ := heL n.val (by have := ZMod.val_lt n; omega)
    exact ⟨x, hx, hxw.trans h.symm⟩

end WordGraph
end GroupApproximation

#audit_axioms GroupApproximation.WordGraph.exists_edgeWalk_of_reflTransGen
#audit_axioms GroupApproximation.WordGraph.edge_apply_eq_of_tail_eq_init
#audit_axioms GroupApproximation.WordGraph.exists_periodic_of_isCyclicEdge
