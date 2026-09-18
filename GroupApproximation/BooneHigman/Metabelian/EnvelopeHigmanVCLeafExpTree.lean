import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCLeafExpFalse
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Pattern refinement of antichain subgroups (lane bh-met-77w)

This is the correct form of single-leaf expansion.  The literal lemma is false: see
`EnvelopeHigmanVCLeafExpFalse`.

A *tree* (`higmanVCLeafExp_IsTree`) is a finite complete prefix antichain obtained from
`{[]}` by single-leaf expansions.  `higmanVCLeafExp_star C T = {c ++ e | c ∈ C, e ∈ T}`
expands every leaf of `C` by the same pattern `T`.

* `higmanVCLeafExp_tree_mem` (**pattern split**): for incomparable `x, y` and a tree `T`,
  the letter `(x, y)` lies in every subgroup that contains all letters `(x e, y e)`,
  `e ∈ T`.  The proof is by induction on `T`, splitting one leaf at a time with the
  relation `(v, w) = ∏ᵢ (v i, w i)`.
* `higmanVCLeafExp_H_le_star` (**monotonicity under arbitrary finite pattern
  refinement**): `H_C ≤ H_{C ⋆ T}` for an antichain `C` and any tree `T`.  This
  generalises the uniform-depth refinement `higmanVCPivotAC_H_le_refine`.

LOUD: the family `T ↦ H_{C ⋆ T}` is not monotone in `T`.  Expanding one leaf `e ∈ T`
under every `c ∈ C` fails already on the letter `(c e, c' e')`, for the reason given in
`EnvelopeHigmanVCLeafExpFalse`.  Only refinement from the base `C` is monotone.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Finite prefix trees: `{[]}` and its closure under single-leaf expansion at a leaf. -/
inductive higmanVCLeafExp_IsTree {d : ℕ} : Finset (List (Fin d)) → Prop
  | root : higmanVCLeafExp_IsTree {[]}
  | expand {T : Finset (List (Fin d))} {c : List (Fin d)} :
      higmanVCLeafExp_IsTree T → c ∈ T → higmanVCLeafExp_IsTree (higmanVCLeafExp_expand T c)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_IsTree

/-- `{[]}` is an antichain. -/
theorem higmanVCLeafExp_root_isAC (d : ℕ) :
    higmanVCTreeNFWitPivot_IsAC ({[]} : Finset (List (Fin d))) := by
  intro u hu v hv huv _
  rw [Finset.mem_singleton] at hu hv
  exact huv (hu.trans hv.symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_root_isAC

/-- A tree is an antichain. -/
theorem higmanVCLeafExp_tree_isAC {d : ℕ} {T : Finset (List (Fin d))}
    (hT : higmanVCLeafExp_IsTree T) : higmanVCTreeNFWitPivot_IsAC T := by
  induction hT with
  | root => exact higmanVCLeafExp_root_isAC d
  | expand _ hc ih => exact higmanVCLeafExp_expand_isAC ih hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_tree_isAC

/-- Appending a common suffix keeps incomparable words incomparable. -/
theorem higmanVCLeafExp_incomp_append {d : ℕ} {x y : List (Fin d)} (h1 : ¬ x <+: y)
    (h2 : ¬ y <+: x) (e : List (Fin d)) : ¬ x ++ e <+: y ++ e := by
  intro h
  rcases List.prefix_or_prefix_of_prefix ((List.prefix_append x e).trans h)
      (List.prefix_append y e) with h' | h'
  · exact h1 h'
  · exact h2 h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_incomp_append

/-- **Pattern split.**  For a tree `T` and incomparable `x, y`, the letter `(x, y)` lies in
every subgroup containing all the letters `(x e, y e)` with `e ∈ T`. -/
theorem higmanVCLeafExp_tree_mem {d : ℕ} {T : Finset (List (Fin d))}
    (hT : higmanVCLeafExp_IsTree T) {K : Subgroup (higmanVCCommon_Q d)} :
    ∀ x y : List (Fin d), ¬ x <+: y → ¬ y <+: x →
      (∀ e ∈ T, higmanVCCommon_mk d (FreeGroup.of (x ++ e, y ++ e)) ∈ K) →
        higmanVCCommon_mk d (FreeGroup.of (x, y)) ∈ K := by
  induction hT with
  | root =>
    intro x y _ _ h
    have h0 := h [] (Finset.mem_singleton_self [])
    rwa [List.append_nil, List.append_nil] at h0
  | @expand _ c _ _ ih =>
    intro x y h1 h2 h
    refine ih x y h1 h2 fun e he => ?_
    by_cases hec : e = c
    · rw [hec, higmanVCCommon_mk_split (higmanVCLeafExp_incomp_append h1 h2 c)
        (higmanVCLeafExp_incomp_append h2 h1 c), higmanVC_splitAll, map_list_prod, List.map_map]
      refine Subgroup.list_prod_mem _ fun q hq => ?_
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
      have h' := h (c ++ [a]) (higmanVCLeafExp_child_mem _ c a)
      rwa [← List.append_assoc, ← List.append_assoc] at h'
    · exact h e (higmanVCLeafExp_mem_expand_of_ne he hec)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_tree_mem
