import Mathlib.Data.Finset.Sort
import GroupApproximation.GGT.DGOTheorem442BBFStandardPath

/-!
# Sorting the finite BBF large-projection set

This file turns the order core of BBF Theorem 3.3(G) into the finite ordered
list used in BBF Proposition 3.7.  At a threshold `K ≥ 12ξ`, the blocker
set for `(X,Z)` is finite.  Its elements have the strict order

`W < U  ↔  5ξ < d_W(X,U)`.

The theorem `exists_bbf_large_projection_list` lists every blocker exactly
once and proves that every earlier list entry precedes every later entry.
This is the list between the two endpoints in the BBF standard path.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- A strict BBF order comparison forces its two vertices to be distinct. -/
theorem ne_of_bbf_before
    (P : ProjectionSystem V) {X W U : V}
    (hbefore : 5 * P.ξ < P.bbfProjDist W X U) :
    W ≠ U := by
  intro hWU
  subst U
  have hzero : P.bbfProjDist W X W = 0 := by
    rw [bbfProjDist, bbfRawProjDist,
      if_pos (Or.inr (Or.inl rfl))]
  rw [hzero] at hbefore
  linarith [P.ξ_pos]

/-- **The finite ordered large-projection set in BBF Proposition 3.7.**
Every blocker of `(X,Z)` occurs exactly once, and entries are pairwise ordered
by the strict comparison from BBF Theorem 3.3(G). -/
theorem exists_bbf_large_projection_list
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z : V} (hXZ : X ≠ Z) :
    ∃ L : List V,
      L.Nodup ∧
      (∀ W, W ∈ L ↔
        W ∈ (ProjectionPerturbation.bbf P).blockers K X Z) ∧
      L.Pairwise (fun W U => 5 * P.ξ < P.bbfProjDist W X U) := by
  classical
  let B : Set V := (ProjectionPerturbation.bbf P).blockers K X Z
  have hKthree : 3 * P.ξ ≤ K := by linarith [hK, P.ξ_pos]
  have hBfin : B.Finite :=
    ProjectionPerturbation.blockers_finite _ hKthree hXZ
  letI : Fintype B := hBfin.fintype
  let r : B → B → Prop := fun W U =>
    W = U ∨ 5 * P.ξ < P.bbfProjDist W X U
  letI : DecidableRel r := Classical.decRel r
  letI : IsTrans B r := ⟨by
    intro W U T hWU hUT
    rcases hWU with hWU | hWU
    · subst U
      exact hUT
    rcases hUT with hUT | hUT
    · subst T
      exact Or.inr hWU
    by_cases hWT : W = T
    · exact Or.inl hWT
    · right
      have hWU' : W ≠ U := P.ne_of_bbf_before hWU
      have hUT' : U ≠ T := P.ne_of_bbf_before hUT
      exact P.bbf_before_trans W.property.1 hWU' hWT
        U.property.1 hUT' T.property.1 hWU hUT⟩
  letI : Std.Antisymm r := ⟨by
    intro W U hWU hUW
    rcases hWU with hWU | hWU
    · exact hWU
    rcases hUW with hUW | hUW
    · exact hUW.symm
    have hWU' : W ≠ U := P.ne_of_bbf_before hWU
    exact (P.bbf_before_asymm W.property.1 hWU' U.property.1 hWU hUW).elim⟩
  letI : Std.Total r := ⟨by
    intro W U
    by_cases hWU : W = U
    · exact Or.inl (Or.inl hWU)
    · have htotal := P.bbf_before_total_on_large hK
        W.property.1 W.property.2.1 U.property.1 U.property.2.1 hWU
        W.property.2.2 U.property.2.2
      rcases htotal with hbefore | hbefore
      · exact Or.inl (Or.inr hbefore)
      · exact Or.inr (Or.inr hbefore)⟩
  let L₀ : List B := Finset.univ.sort r
  let L : List V := L₀.map ((↑) : B → V)
  refine ⟨L, ?_, ?_, ?_⟩
  · dsimp [L]
    exact (Finset.sort_nodup Finset.univ r).map Subtype.coe_injective
  · intro W
    constructor
    · intro hW
      obtain ⟨W₀, hW₀, hcoe⟩ := List.mem_map.mp hW
      rw [← hcoe]
      exact W₀.property
    · intro hW
      let W₀ : B := ⟨W, hW⟩
      have hW₀ : W₀ ∈ L₀ := by
        dsimp [L₀]
        exact (Finset.mem_sort r).mpr (Finset.mem_univ W₀)
      exact List.mem_map.mpr ⟨W₀, hW₀, rfl⟩
  · have hpair : L₀.Pairwise r := by
      dsimp [L₀]
      exact Finset.pairwise_sort Finset.univ r
    have hne : L₀.Pairwise (fun W U : B => W ≠ U) := by
      exact Finset.sort_nodup Finset.univ r
    have hstrict :
        L₀.Pairwise (fun W U : B =>
          5 * P.ξ < P.bbfProjDist W X U) := by
      exact (hpair.and hne).imp fun W U h => h.1.resolve_left h.2
    dsimp [L]
    rw [List.pairwise_map]
    exact hstrict

/-- Consecutive entries in a list supplied by
`exists_bbf_large_projection_list` have no large projection strictly between
them.  This is the list-theoretic input to `bbf_graph_adj_of_consecutive`. -/
theorem bbf_no_between_of_large_projection_list
    (P : ProjectionSystem V) {K : ℝ}
    {X Z : V} {L L₀ L₁ : List V} {Y₀ Y₁ W : V}
    (hmem : ∀ T, T ∈ L ↔
      T ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hpair : L.Pairwise (fun A B =>
      5 * P.ξ < P.bbfProjDist A X B))
    (hL : L = L₀ ++ Y₀ :: Y₁ :: L₁)
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hWY₀ : W ≠ Y₀) (hWY₁ : W ≠ Y₁) :
    ¬ (5 * P.ξ < P.bbfProjDist Y₀ X W ∧
      5 * P.ξ < P.bbfProjDist W X Y₁) := by
  intro hbetween
  have hY₀mem : Y₀ ∈ L := by rw [hL]; simp
  have hY₁mem : Y₁ ∈ L := by rw [hL]; simp
  have hY₀large := (hmem Y₀).mp hY₀mem
  have hY₁large := (hmem Y₁).mp hY₁mem
  have hWmem : W ∈ L := (hmem W).mpr hW
  rw [hL] at hpair hWmem
  have hcases : W ∈ L₀ ∨ W = Y₀ ∨ W = Y₁ ∨ W ∈ L₁ := by
    simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
      or_assoc] using hWmem
  rcases hcases with hWL₀ | hWY₀' | hWY₁' | hWL₁
  · have hcross := (List.pairwise_append.mp hpair).2.2
    have hWY₀before : 5 * P.ξ < P.bbfProjDist W X Y₀ :=
      hcross W hWL₀ Y₀ (by simp)
    exact (P.bbf_before_asymm hW.1 hWY₀ hY₀large.1
      hWY₀before) hbetween.1
  · exact hWY₀ hWY₀'
  · exact hWY₁ hWY₁'
  · have hpair' :
        ((L₀ ++ [Y₀, Y₁]) ++ L₁).Pairwise (fun A B =>
          5 * P.ξ < P.bbfProjDist A X B) := by
      simpa only [List.append_assoc, List.append_cons, List.append_nil] using hpair
    have hcross := (List.pairwise_append.mp hpair').2.2
    have hY₁Wbefore : 5 * P.ξ < P.bbfProjDist Y₁ X W :=
      hcross Y₁ (by simp) W hWL₁
    exact (P.bbf_before_asymm hY₁large.1 hWY₁.symm hW.1
      hY₁Wbefore) hbetween.2

end ProjectionSystem
end GGT
end GroupApproximation
