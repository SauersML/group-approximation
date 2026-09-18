import GroupApproximation.Kourovka1759.Equi

/-!
# Split trees

A split tree is a leaf or a node that splits its box into `k` children `j + kℤ` (placed inside
the box). Its leaves, placed inside `ℤ`, form a partition of `ℤ` into boxes. Two trees are
equivalent when their leaf lists are (`Equi`). Replacing a child by an equivalent tree preserves
equivalence.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

/-- Split trees. -/
inductive STree : Type
  | leaf : STree
  | node (k : ℕ) (c : Fin k → STree) : STree

namespace STree

/-- The leaves of a tree rooted at `ℤ`, as boxes. -/
def leaves : STree → List Box
  | leaf => [univ]
  | node k c => (List.finRange k).flatMap fun j => (leaves (c j)).map (place (child k j))

/-- The multiset of arities of all internal nodes. -/
def nodes : STree → Multiset ℕ
  | leaf => 0
  | node k c => k ::ₘ ∑ j, nodes (c j)

/-- The arity of the root (`0` for a leaf). -/
def root : STree → ℕ
  | leaf => 0
  | node k _ => k

/-- Every node splits into at least two children. -/
def WF : STree → Prop
  | leaf => True
  | node k c => 2 ≤ k ∧ ∀ j, WF (c j)

/-- Equivalence of trees: some element of `CT(ℤ)` maps the leaves of one canonically onto the
leaves of the other. -/
def TEq (s t : STree) : Prop := Equi s.leaves t.leaves

theorem TEq.refl (t : STree) : TEq t t := Equi.refl _
theorem TEq.symm {s t : STree} (h : TEq s t) : TEq t s := Equi.symm h
theorem TEq.trans {s t u : STree} (h₁ : TEq s t) (h₂ : TEq t u) : TEq s u := Equi.trans h₁ h₂

theorem TEq.of_perm {s t : STree} (h : s.leaves.Perm t.leaves) : TEq s t := Equi.of_perm h

theorem cover : ∀ t : STree, WF t → ∀ n, ∃ B ∈ t.leaves, B.Mem n
  | leaf, _, n => ⟨univ, List.mem_singleton_self _, univ_mem n⟩
  | node k c, ⟨hk, hc⟩, n => by
    have hk0 : 0 < k := by omega
    obtain ⟨B, hB, hBn⟩ := cover (c (classOf k hk0 n)) (hc _) (n / (child k (classOf k hk0 n)).m)
    refine ⟨place (child k (classOf k hk0 n)) B, ?_, mem_place.2 ⟨mem_classOf k hk0 n, hBn⟩⟩
    simp only [leaves, List.mem_flatMap, List.mem_map]
    exact ⟨_, List.mem_finRange _, B, hB, rfl⟩

theorem pairwise : ∀ t : STree, t.leaves.Pairwise Box.Disj
  | leaf => List.pairwise_singleton _ _
  | node k c => by
    simp only [leaves]
    rw [List.pairwise_flatMap]
    refine ⟨fun j _ => ?_, ?_⟩
    · rw [List.pairwise_map]; exact (pairwise (c j)).imp fun h => disj_place h
    · refine List.Pairwise.imp (fun {i j} hij => ?_) (List.nodup_finRange k)
      intro x hx y hy
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hy
      exact disj_place_of (child_disj k hij)

theorem flatMap_congr' {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The leaves of a node, with the block of child `j` moved to the end. -/
theorem leaves_perm_extract (k : ℕ) (c : Fin k → STree) (j : Fin k) :
    (node k c).leaves.Perm
      ((((List.finRange k).erase j).flatMap fun i => (c i).leaves.map (place (child k i))) ++
        (c j).leaves.map (place (child k j))) := by
  have h := (List.perm_cons_erase (List.mem_finRange j)).flatMap_right
    (fun i => (c i).leaves.map (place (child k i)))
  rw [List.flatMap_cons] at h
  exact h.trans List.perm_append_comm

theorem mem_erase_ne {k : ℕ} {i j : Fin k} (hi : i ∈ (List.finRange k).erase j) : i ≠ j :=
  ((List.nodup_finRange k).mem_erase_iff.1 hi).1

/-- Boxes of the other children are disjoint from child `j`. -/
theorem others_disj (k : ℕ) (c : Fin k → STree) (j : Fin k) :
    ∀ E ∈ (((List.finRange k).erase j).flatMap fun i => (c i).leaves.map (place (child k i))),
      E.Disj (child k j) := by
  intro E hE
  obtain ⟨i, hi, hE⟩ := List.mem_flatMap.1 hE
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 hE
  exact fun n hn hj => child_disj k (mem_erase_ne hi) n (place_mem_of hn) hj

theorem teq_update (k : ℕ) (c : Fin k → STree) (j : Fin k) (s : STree) (h : TEq (c j) s) :
    TEq (node k c) (node k (Function.update c j s)) := by
  classical
  have h1 := leaves_perm_extract k c j
  have h2 := leaves_perm_extract k (Function.update c j s) j
  rw [Function.update_self] at h2
  rw [flatMap_congr' (g := fun i => (c i).leaves.map (place (child k i))) (fun i hi => by
    rw [Function.update_of_ne (mem_erase_ne hi)])] at h2
  exact ((Equi.local_box (others_disj k c j) h).perm_left h1.symm).perm_right h2.symm

theorem teq_congr (k : ℕ) (c c' : Fin k → STree) (h : ∀ j, TEq (c j) (c' j)) :
    TEq (node k c) (node k c') := by
  classical
  have key : ∀ S : Finset (Fin k),
      TEq (node k c) (node k fun i => if i ∈ S then c' i else c i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using TEq.refl (node k c)
    | insert a S ha ih =>
      have heq : (fun i => if i ∈ insert a S then c' i else c i) =
          Function.update (fun i => if i ∈ S then c' i else c i) a (c' a) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp
        · simp [Function.update_of_ne hi, hi]
      rw [heq]
      refine ih.trans (teq_update k _ a (c' a) ?_)
      simpa [ha] using h a
  simpa using key Finset.univ

end STree

end GroupApproximation.Kourovka1759
