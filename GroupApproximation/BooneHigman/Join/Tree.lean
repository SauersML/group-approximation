import GroupApproximation.BooneHigman.Join.NKer

/-!
# Finite binary trees and their leaf codes (lane bh-pal-met-join)

* `BTree`: finite binary trees.  `leaves T` is the list of leaf addresses, a complete prefix code
  (`leaves_isAC`, `leaves_cover`).
* `expand T w` splits the leaf at address `w`; its leaves are those of `T` with `w` replaced by
  `w0` and `w1` (`mem_leaves_expand`).
* `rdepth` / `ldepth`: the rightmost leaf is `1^rdepth` and the leftmost is `0^ldepth`.
* `lset T` is the leaf code as a `Finset`, and `IsAC (lset T)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Finite binary trees. -/
inductive BTree : Type
  | leaf : BTree
  | node : BTree → BTree → BTree

namespace BTree

/-- The leaf addresses. -/
def leaves : BTree → List (List (Fin 2))
  | leaf => [[]]
  | node l r => l.leaves.map (List.cons 0) ++ r.leaves.map (List.cons 1)

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.leaves

theorem mem_leaves_node {l r : BTree} {c : List (Fin 2)} :
    c ∈ (node l r).leaves ↔ (∃ c' ∈ l.leaves, c = 0 :: c') ∨ (∃ c' ∈ r.leaves, c = 1 :: c') := by
  simp only [leaves, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨c', h, rfl⟩ | ⟨c', h, rfl⟩)
    · exact Or.inl ⟨c', h, rfl⟩
    · exact Or.inr ⟨c', h, rfl⟩
  · rintro (⟨c', h, rfl⟩ | ⟨c', h, rfl⟩)
    · exact Or.inl ⟨c', h, rfl⟩
    · exact Or.inr ⟨c', h, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.mem_leaves_node

/-- The leaves form an antichain. -/
theorem leaves_isAC : ∀ T : BTree, ∀ u ∈ T.leaves, ∀ v ∈ T.leaves, u ≠ v → ¬ u <+: v
  | leaf, u, hu, v, hv, hne => by
    simp only [leaves, List.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) hne
  | node l r, u, hu, v, hv, hne => by
    rcases mem_leaves_node.mp hu with ⟨u', hu', rfl⟩ | ⟨u', hu', rfl⟩ <;>
      rcases mem_leaves_node.mp hv with ⟨v', hv', rfl⟩ | ⟨v', hv', rfl⟩
    · intro h
      exact leaves_isAC l u' hu' v' hv' (fun e => hne (by rw [e]))
        ((List.prefix_cons_inj 0).mp h)
    · intro h
      exact absurd (List.cons_prefix_cons.mp h).1 (by decide)
    · intro h
      exact absurd (List.cons_prefix_cons.mp h).1 (by decide)
    · intro h
      exact leaves_isAC r u' hu' v' hv' (fun e => hne (by rw [e]))
        ((List.prefix_cons_inj 1).mp h)

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.leaves_isAC

theorem isStreamPrefix_cons {a : Fin 2} {c : List (Fin 2)} {x : Cantor (Fin 2)}
    (h0 : x 0 = a) (h : IsStreamPrefix c (dropN 1 x)) : IsStreamPrefix (a :: c) x := by
  intro k hk
  cases k with
  | zero => exact h0
  | succ k =>
    have h' := h k (by simpa using hk)
    simp only [dropN] at h'
    exact h'

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.isStreamPrefix_cons

/-- The leaves cover the boundary. -/
theorem leaves_cover : ∀ (T : BTree) (x : Cantor (Fin 2)), ∃ c ∈ T.leaves, IsStreamPrefix c x
  | leaf, x => ⟨[], by simp [leaves], fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | node l r, x => by
    rcases fin2_cases (x 0) with h0 | h0
    · obtain ⟨c, hc, hp⟩ := leaves_cover l (dropN 1 x)
      exact ⟨0 :: c, mem_leaves_node.mpr (Or.inl ⟨c, hc, rfl⟩), isStreamPrefix_cons h0 hp⟩
    · obtain ⟨c, hc, hp⟩ := leaves_cover r (dropN 1 x)
      exact ⟨1 :: c, mem_leaves_node.mpr (Or.inr ⟨c, hc, rfl⟩), isStreamPrefix_cons h0 hp⟩

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.leaves_cover

/-- Split the leaf at address `w` (a no-op if `w` is not a leaf address). -/
def expand : BTree → List (Fin 2) → BTree
  | leaf, [] => node leaf leaf
  | leaf, _ :: _ => leaf
  | node l r, [] => node l r
  | node l r, a :: w => if a = 0 then node (l.expand w) r else node l (r.expand w)

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.expand

theorem expand_node_zero (l r : BTree) (w : List (Fin 2)) :
    (node l r).expand (0 :: w) = node (l.expand w) r := by
  simp [expand]

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.expand_node_zero

theorem expand_node_one (l r : BTree) (w : List (Fin 2)) :
    (node l r).expand (1 :: w) = node l (r.expand w) := by
  simp [expand]

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.expand_node_one

/-- **The leaves of an expansion.** -/
theorem mem_leaves_expand : ∀ (T : BTree) {w : List (Fin 2)}, w ∈ T.leaves →
    ∀ c, c ∈ (T.expand w).leaves ↔ (c ∈ T.leaves ∧ c ≠ w) ∨ c = w ++ [0] ∨ c = w ++ [1]
  | leaf, w, hw, c => by
    simp only [leaves, List.mem_singleton] at hw
    subst hw
    show c ∈ ([[0], [1]] : List (List (Fin 2))) ↔
      (c ∈ ([[]] : List (List (Fin 2))) ∧ c ≠ []) ∨ c = [] ++ [0] ∨ c = [] ++ [1]
    simp only [List.mem_cons, List.mem_singleton, List.nil_append, List.not_mem_nil, or_false]
    tauto
  | node l r, w, hw, c => by
    rcases mem_leaves_node.mp hw with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · rw [expand_node_zero, mem_leaves_node, mem_leaves_node]
      constructor
      · rintro (⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩)
        · rcases (mem_leaves_expand l hw' c').mp hc' with ⟨h1, h2⟩ | rfl | rfl
          · exact Or.inl ⟨Or.inl ⟨c', h1, rfl⟩, fun e => h2 (List.cons_injective e)⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        · exact Or.inl ⟨Or.inr ⟨c', hc', rfl⟩, fun e => absurd (List.cons.inj e).1 (by decide)⟩
      · rintro (⟨⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩, hne⟩ | rfl | rfl)
        · exact Or.inl ⟨c', (mem_leaves_expand l hw' c').mpr
            (Or.inl ⟨hc', fun e => hne (by rw [e])⟩), rfl⟩
        · exact Or.inr ⟨c', hc', rfl⟩
        · exact Or.inl ⟨w' ++ [0], (mem_leaves_expand l hw' _).mpr (Or.inr (Or.inl rfl)), rfl⟩
        · exact Or.inl ⟨w' ++ [1], (mem_leaves_expand l hw' _).mpr (Or.inr (Or.inr rfl)), rfl⟩
    · rw [expand_node_one, mem_leaves_node, mem_leaves_node]
      constructor
      · rintro (⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩)
        · exact Or.inl ⟨Or.inl ⟨c', hc', rfl⟩, fun e => absurd (List.cons.inj e).1 (by decide)⟩
        · rcases (mem_leaves_expand r hw' c').mp hc' with ⟨h1, h2⟩ | rfl | rfl
          · exact Or.inl ⟨Or.inr ⟨c', h1, rfl⟩, fun e => h2 (List.cons_injective e)⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
      · rintro (⟨⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩, hne⟩ | rfl | rfl)
        · exact Or.inl ⟨c', hc', rfl⟩
        · exact Or.inr ⟨c', (mem_leaves_expand r hw' c').mpr
            (Or.inl ⟨hc', fun e => hne (by rw [e])⟩), rfl⟩
        · exact Or.inr ⟨w' ++ [0], (mem_leaves_expand r hw' _).mpr (Or.inr (Or.inl rfl)), rfl⟩
        · exact Or.inr ⟨w' ++ [1], (mem_leaves_expand r hw' _).mpr (Or.inr (Or.inr rfl)), rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.mem_leaves_expand

/-- The depth of the rightmost leaf. -/
def rdepth : BTree → ℕ
  | leaf => 0
  | node _ r => r.rdepth + 1

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.rdepth

/-- The depth of the leftmost leaf. -/
def ldepth : BTree → ℕ
  | leaf => 0
  | node l _ => l.ldepth + 1

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.ldepth

theorem rightmost_mem : ∀ T : BTree, List.replicate T.rdepth 1 ∈ T.leaves
  | leaf => by simp [leaves, rdepth]
  | node _ r => mem_leaves_node.mpr (Or.inr ⟨_, rightmost_mem r, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.rightmost_mem

theorem leftmost_mem : ∀ T : BTree, List.replicate T.ldepth 0 ∈ T.leaves
  | leaf => by simp [leaves, ldepth]
  | node l _ => mem_leaves_node.mpr (Or.inl ⟨_, leftmost_mem l, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.leftmost_mem

/-- The leaf code as a finite set. -/
def lset (T : BTree) : Finset (List (Fin 2)) := T.leaves.toFinset

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.lset

theorem mem_lset {T : BTree} {c : List (Fin 2)} : c ∈ T.lset ↔ c ∈ T.leaves :=
  List.mem_toFinset

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.mem_lset

theorem lset_isAC (T : BTree) : IsAC T.lset := fun u hu v hv hne =>
  leaves_isAC T u (mem_lset.mp hu) v (mem_lset.mp hv) hne

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.lset_isAC

/-- A bound on the lengths of the leaves. -/
def depth : BTree → ℕ
  | leaf => 0
  | node l r => max l.depth r.depth + 1

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.depth

theorem length_le_depth : ∀ (T : BTree) {c : List (Fin 2)}, c ∈ T.leaves → c.length ≤ T.depth
  | leaf, c, hc => by
    simp only [leaves, List.mem_singleton] at hc
    subst hc
    simp [depth]
  | node l r, c, hc => by
    rcases mem_leaves_node.mp hc with ⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩
    · have := length_le_depth l hc'
      simp only [List.length_cons, depth]
      omega
    · have := length_le_depth r hc'
      simp only [List.length_cons, depth]
      omega

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.length_le_depth

/-- `u` lies at or below a leaf of `T`. -/
def AtOrBelow (T : BTree) (u : List (Fin 2)) : Prop := ∃ c ∈ T.leaves, c <+: u

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.AtOrBelow

/-- Every word at least as long as the depth lies at or below a leaf. -/
theorem atOrBelow_of_depth_le (T : BTree) {u : List (Fin 2)} (hu : T.depth ≤ u.length) :
    T.AtOrBelow u := by
  obtain ⟨c, hc, hp⟩ := leaves_cover T (prepend u (fun _ => 0))
  exact ⟨c, hc, prefix_of_isStreamPrefix_of_length_le hp (isStreamPrefix_prepend u _)
    ((length_le_depth T hc).trans hu)⟩

#audit_axioms GroupApproximation.BooneHigman.Join.BTree.atOrBelow_of_depth_le

end BTree

end GroupApproximation.BooneHigman.Join
