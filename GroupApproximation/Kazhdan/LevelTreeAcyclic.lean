import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import GroupApproximation.Meta.AxiomGuard

/-!
# A graph with a unique-parent level function is acyclic

The combinatorial core of the Bruhat--Tits tree step in the rank-two remark after
`prop:torsion-defect-ring` of `non_mf_groups_exist.tex` (tex lines 1146--1150).

Let `lvl : V → ℕ` be a level function on a simple graph such that adjacent
vertices have levels differing by exactly one, and every vertex has at most one
neighbour one level below it.  Then the graph has no cycle: a vertex of maximal
level on a cycle has both of its cycle neighbours one level below it, so they
coincide, which a cycle forbids (`IsCycle.snd_ne_penultimate`).

Along any walk the level changes by at most one per step, so the level
difference is a lower bound for the graph distance.
-/

namespace GroupApproximation
namespace LevelTree

universe u

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- **A unique-parent level function makes a graph acyclic.** -/
theorem isAcyclic_of_level (lvl : V → ℕ)
    (hadj : ∀ ⦃x y : V⦄, G.Adj x y → lvl y = lvl x + 1 ∨ lvl x = lvl y + 1)
    (huniq : ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj x z → lvl y + 1 = lvl x → lvl z + 1 = lvl x →
      y = z) :
    G.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨w, hw, hmax⟩ := c.support.toFinset.exists_max_image lvl ⟨v, by simp⟩
  have hwc : w ∈ c.support := List.mem_toFinset.mp hw
  let c' := c.rotate w hwc
  have hc' : c'.IsCycle := IsCycle.rotate hwc hc
  have hnil : ¬ c'.Nil := hc'.not_nil
  have h1 : G.Adj w c'.snd := Walk.adj_snd hnil
  have h2 : G.Adj w c'.penultimate := (Walk.adj_penultimate hnil).symm
  have hlow : ∀ y, G.Adj w y → y ∈ c.support → lvl y + 1 = lvl w := by
    intro y hy hyc
    have hle := hmax y (List.mem_toFinset.mpr hyc)
    rcases hadj hy with h | h
    · omega
    · exact h.symm
  have hs : c'.snd ∈ c.support :=
    (Walk.mem_support_rotate_iff c w hwc).mp (c'.getVert_mem_support 1)
  have hp : c'.penultimate ∈ c.support :=
    (Walk.mem_support_rotate_iff c w hwc).mp (c'.getVert_mem_support _)
  exact hc'.snd_ne_penultimate (huniq h1 h2 (hlow _ h1 hs) (hlow _ h2 hp))

/-- Along a walk the level rises by at most the length. -/
theorem level_le_add_length (lvl : V → ℕ)
    (hadj : ∀ ⦃x y : V⦄, G.Adj x y → lvl y = lvl x + 1 ∨ lvl x = lvl y + 1) :
    ∀ {x y : V} (p : G.Walk x y), lvl y ≤ lvl x + p.length := by
  intro x y p
  induction p with
  | nil => simp
  | cons h p ih =>
      rw [Walk.length_cons]
      rcases hadj h with h' | h' <;> omega

/-- **The level difference bounds the graph distance from below.** -/
theorem level_le_add_dist (lvl : V → ℕ)
    (hadj : ∀ ⦃x y : V⦄, G.Adj x y → lvl y = lvl x + 1 ∨ lvl x = lvl y + 1)
    (hconn : G.Connected) (x y : V) : lvl y ≤ lvl x + G.dist x y := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  rw [← hp]
  exact level_le_add_length lvl hadj p

/-- A connected graph with a unique-parent level function is a tree. -/
theorem isTree_of_level (lvl : V → ℕ) (hconn : G.Connected)
    (hadj : ∀ ⦃x y : V⦄, G.Adj x y → lvl y = lvl x + 1 ∨ lvl x = lvl y + 1)
    (huniq : ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj x z → lvl y + 1 = lvl x → lvl z + 1 = lvl x →
      y = z) :
    G.IsTree :=
  ⟨hconn, isAcyclic_of_level lvl hadj huniq⟩

end LevelTree
end GroupApproximation

#audit_axioms GroupApproximation.LevelTree.isTree_of_level
#audit_axioms GroupApproximation.LevelTree.level_le_add_dist
