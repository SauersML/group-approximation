import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleInternal
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleOrderedProd
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleSeed
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Lex
import GroupApproximation.Meta.AxiomGuard

/-!
# Canonical coherent code-shuffle lifts

Order internal nodes by decreasing depth, then lexicographically. The product
of their prescribed shuffles depends only on the code. Expanding a leaf
multiplies this product on the left by that leaf's shuffle, exactly in the
presented quotient. No boundary-faithfulness assumption is used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Decreasing depth, with a fixed lexical tie-breaker. -/
def higSw_nodeKey (d : ℕ) : List (Fin d) ↪ Lex (ℕᵒᵈ × List (Fin d)) where
  toFun c := toLex (OrderDual.toDual c.length, c)
  inj' := by
    intro c e h
    exact congrArg (fun p => (ofLex p).2) h

/-- The canonical lift formed from the sorted internal-node set. -/
noncomputable def higSw_codeLift {d : ℕ} (C : Finset (List (Fin d))) :
    higmanVCCommon_Q d :=
  ((((higSw_internal C).map (higSw_nodeKey d)).sort (· ≤ ·)).map
    fun p => higSw_shuffle d (ofLex p).2).prod

theorem higSw_codeLift_root (d : ℕ) :
    higSw_codeLift ({[]} : Finset (List (Fin d))) = 1 := by
  simp [higSw_codeLift, higSw_internal]

/-- Exact coherence: expansion adds the prescribed factor on the left. -/
theorem higSw_codeLift_expand {d : ℕ} (hd : 0 < d)
    {C : Finset (List (Fin d))} {c : List (Fin d)}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hc : c ∈ C) :
    higSw_codeLift (higmanVCLeafExp_expand C c) =
      higSw_shuffle d c * higSw_codeLift C := by
  have hn : higSw_nodeKey d c ∉ (higSw_internal C).map (higSw_nodeKey d) := by
    intro hm
    obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp hm
    exact higSw_leaf_not_internal hC hc ((higSw_nodeKey d).injective heq ▸ hu)
  unfold higSw_codeLift
  rw [higSw_internal_expand hd hc, Finset.map_insert]
  apply higSw_sort_prod_insert _ _ hn (fun p => higSw_shuffle d (ofLex p).2)
  intro p hp hpc
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hp
  have hlen : c.length ≤ u.length :=
    Prod.Lex.monotone_fst _ _ (le_of_lt hpc)
  have hi := higSw_internal_deep_incomp hC hc hu hlen
  exact higSw_shuffle_commute hi.1 hi.2

/-- The canonical lift has the code-shuffle action for every finite expansion tree. -/
theorem higSw_codeLift_action {d : ℕ} (hd : 0 < d)
    {C : Finset (List (Fin d))} (hC : higmanVCLeafExp_IsTree C) :
    higSw_codeAction C (higSw_codeLift C) := by
  induction hC with
  | root =>
    rw [higSw_codeLift_root]
    exact higSw_codeAction_root d
  | @expand C c hC hc ih =>
    rw [higSw_codeLift_expand hd (higmanVCLeafExp_tree_isAC hC) hc]
    exact higSw_codeAction_expand (higmanVCLeafExp_tree_isAC hC) hc ih

/-- The canonical lift supplies the generator identity on a seed code. -/
theorem higSw_codeLift_swap_naturality {d : ℕ} (hd : 1 < d)
    {C : Finset (List (Fin d))} (hC : higmanVCLeafExp_IsTree C)
    {x y : List (Fin d)} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    higSw_codeLift C * higmanVCCommon_mk d (FreeGroup.of (x, y)) =
      higSw_diag d (higmanVCCommon_mk d (FreeGroup.of (x, y))) * higSw_codeLift C :=
  higSw_codeAction_swap_naturality hd (higmanVCLeafExp_tree_isAC hC)
    (higSw_codeLift_action (by omega) hC) hx hy hxy

/-- Matched leaf expansion preserves naturality for these canonical lifts. -/
theorem higSw_codeLift_expand_naturality {d : ℕ} (hd : 1 < d)
    {C D : Finset (List (Fin d))} (hC : higmanVCTreeNFWitPivot_IsAC C)
    (hD : higmanVCTreeNFWitPivot_IsAC D) {c e : List (Fin d)}
    (hc : c ∈ C) (he : e ∈ D) (q : higmanVCCommon_Q d)
    (hcone : MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d))) c e)
    (hn : higSw_codeLift D * q = higSw_diag d q * higSw_codeLift C) :
    higSw_codeLift (higmanVCLeafExp_expand D e) * q =
      higSw_diag d q * higSw_codeLift (higmanVCLeafExp_expand C c) := by
  rw [higSw_codeLift_expand (by omega) hD he, higSw_codeLift_expand (by omega) hC hc]
  exact higSw_shuffle_expansion_naturality hd q _ _ hcone hn

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeLift_expand
#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeLift_action
#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeLift_swap_naturality
#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeLift_expand_naturality

end GroupApproximation.BooneHigman.Metabelian.Envelope
