import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import GroupApproximation.GGT.DGOTheorem442BBFSortedLarge

/-!
# The BBF standard walk

This file completes the path construction in Bestvina--Bromberg--Fujiwara
Proposition 3.7.  The finite set of large projections of `(X,Z)` is sorted by
the BBF order, the two endpoints are added, and the endpoint and consecutive
edge lemmas prove that the resulting vertex list is the support of a walk in
the projection graph.

The resulting support is exactly

`X :: orderedLargeProjections ++ [Z]`.

This concrete walk is the path used in the later guard and bottleneck
arguments.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- The first entry of an ordered large-projection list is minimal in the BBF
order. -/
theorem bbf_head_minimal_of_large_projection_list
    (P : ProjectionSystem V) {K : ℝ} {X Z Y : V} {L : List V}
    (hmem : ∀ T, T ∈ Y :: L ↔
      T ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hpair : (Y :: L).Pairwise (fun A B =>
      5 * P.ξ < P.bbfProjDist A X B)) :
    ∀ W,
      W ∈ (ProjectionPerturbation.bbf P).blockers K X Z →
      W ≠ Y → ¬ 5 * P.ξ < P.bbfProjDist W X Y := by
  intro W hW hWY hWYbefore
  have hYlarge := (hmem Y).mp (List.mem_cons_self)
  have hWmem : W ∈ Y :: L := (hmem W).mpr hW
  have hWL : W ∈ L := (List.mem_cons.mp hWmem).resolve_left hWY
  have hYWbefore : 5 * P.ξ < P.bbfProjDist Y X W :=
    List.rel_of_pairwise_cons hpair hWL
  exact (P.bbf_before_asymm hW.1 hWY hYlarge.1 hWYbefore) hYWbefore

/-- The last entry of an ordered large-projection list is maximal in the BBF
order. -/
theorem bbf_getLast_maximal_of_large_projection_list
    (P : ProjectionSystem V) {K : ℝ} {X Z : V} {L : List V}
    (hL : L ≠ [])
    (hmem : ∀ T, T ∈ L ↔
      T ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hpair : L.Pairwise (fun A B =>
      5 * P.ξ < P.bbfProjDist A X B)) :
    ∀ W,
      W ∈ (ProjectionPerturbation.bbf P).blockers K X Z →
      W ≠ L.getLast hL →
      ¬ 5 * P.ξ < P.bbfProjDist (L.getLast hL) X W := by
  intro W hW hWlast hlastWbefore
  let T : V := L.getLast hL
  have hTmem : T ∈ L := by
    exact List.getLast_mem hL
  have hTlarge := (hmem T).mp hTmem
  have hWmem : W ∈ L := (hmem W).mpr hW
  have hsplit : L.dropLast ++ [T] = L := by
    exact List.dropLast_concat_getLast hL
  have hWdrop : W ∈ L.dropLast := by
    rw [← hsplit] at hWmem
    rcases List.mem_append.mp hWmem with hWdrop | hWsingleton
    · exact hWdrop
    · have hWT : W = T := List.mem_singleton.mp hWsingleton
      exact (hWlast hWT).elim
  have hpair' : (L.dropLast ++ [T]).Pairwise (fun A B =>
      5 * P.ξ < P.bbfProjDist A X B) := by
    rw [hsplit]
    exact hpair
  have hcross := (List.pairwise_append.mp hpair').2.2
  have hWTbefore : 5 * P.ξ < P.bbfProjDist W X T :=
    hcross W hWdrop T (List.mem_singleton_self T)
  have hWT : W ≠ T := by
    exact hWlast
  exact (P.bbf_before_asymm hW.1 hWT hTlarge.1 hWTbefore) hlastWbefore

/-- Consecutive entries of an ordered large-projection list are adjacent in
the BBF projection graph. -/
theorem bbf_large_projection_list_isChain
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z : V} {L : List V}
    (hmem : ∀ T, T ∈ L ↔
      T ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hpair : L.Pairwise (fun A B =>
      5 * P.ξ < P.bbfProjDist A X B)) :
    L.IsChain ((ProjectionPerturbation.bbf P).graph K).Adj := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro Y₀ Y₁ L₀ L₁ hdecomp
  have hY₀mem : Y₀ ∈ L := by rw [hdecomp]; simp
  have hY₁mem : Y₁ ∈ L := by rw [hdecomp]; simp
  have hY₀large := (hmem Y₀).mp hY₀mem
  have hY₁large := (hmem Y₁).mp hY₁mem
  have hpair' := hpair
  rw [hdecomp] at hpair'
  have htail := (List.pairwise_append.mp hpair').2.1
  have hbefore : 5 * P.ξ < P.bbfProjDist Y₀ X Y₁ :=
    List.rel_of_pairwise_cons htail (List.mem_cons_self)
  have hY₀Y₁ : Y₀ ≠ Y₁ := P.ne_of_bbf_before hbefore
  apply P.bbf_graph_adj_of_consecutive hK hY₀large hY₁large
    hY₀Y₁ hbefore
  intro W hW hWY₀ hWY₁
  exact P.bbf_no_between_of_large_projection_list hmem hpair hdecomp
    hW hWY₀ hWY₁

/-- **The standard walk of BBF Proposition 3.7.**  Its interior vertices are
exactly the large projections of `(X,Z)`, in their BBF order. -/
theorem exists_bbf_standard_walk
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z : V} (hXZ : X ≠ Z) :
    ∃ L : List V,
      L.Nodup ∧
      (∀ W, W ∈ L ↔
        W ∈ (ProjectionPerturbation.bbf P).blockers K X Z) ∧
      L.Pairwise (fun W U => 5 * P.ξ < P.bbfProjDist W X U) ∧
      ∃ p : ((ProjectionPerturbation.bbf P).graph K).Walk X Z,
        p.support = X :: L ++ [Z] := by
  obtain ⟨L, hnodup, hmem, hpair⟩ :=
    P.exists_bbf_large_projection_list hK hXZ
  refine ⟨L, hnodup, hmem, hpair, ?_⟩
  cases L with
  | nil =>
      have hempty : (ProjectionPerturbation.bbf P).blockers K X Z = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro W hW
        have hmemNil : W ∈ ([] : List V) := (hmem W).mpr hW
        exact List.not_mem_nil hmemNil
      have hadj : ((ProjectionPerturbation.bbf P).graph K).Adj X Z :=
        (ProjectionPerturbation.graph_adj_iff_blockers_eq_empty _ K X Z).mpr
          ⟨hXZ, hempty⟩
      refine ⟨hadj.toWalk, ?_⟩
      simp
  | cons Y L =>
      have hLne : Y :: L ≠ [] := List.cons_ne_nil Y L
      have hYlarge := (hmem Y).mp (List.mem_cons_self)
      have hminimal :=
        P.bbf_head_minimal_of_large_projection_list hmem hpair
      have hleft := P.bbf_graph_adj_left_endpoint_of_minimal
        hK hYlarge hminimal
      have hchain := P.bbf_large_projection_list_isChain hK hmem hpair
      have hchainLeft : (X :: Y :: L).IsChain
          ((ProjectionPerturbation.bbf P).graph K).Adj :=
        List.IsChain.cons_of_ne_nil hLne hchain hleft
      have hlastLarge : (Y :: L).getLast hLne ∈
          (ProjectionPerturbation.bbf P).blockers K X Z := by
        apply (hmem ((Y :: L).getLast hLne)).mp
        exact List.getLast_mem hLne
      have hmaximal :=
        P.bbf_getLast_maximal_of_large_projection_list hLne hmem hpair
      have hright := P.bbf_graph_adj_right_endpoint_of_maximal
        hK hlastLarge hmaximal
      have hfull : ((X :: Y :: L) ++ [Z]).IsChain
          ((ProjectionPerturbation.bbf P).graph K).Adj := by
        apply hchainLeft.append (List.isChain_singleton Z)
        intro A hA B hB
        have hAeq : (Y :: L).getLast hLne = A := by
          simpa [hLne] using hA
        have hBeq : Z = B := by simpa using hB
        rw [← hAeq, ← hBeq]
        exact hright
      let q := SimpleGraph.Walk.ofSupport ((X :: Y :: L) ++ [Z])
        (by simp) hfull
      let p : ((ProjectionPerturbation.bbf P).graph K).Walk X Z :=
        q.copy (by simp [q]) (by simp [q])
      refine ⟨p, ?_⟩
      simp [p, q]

end ProjectionSystem
end GGT
end GroupApproximation
