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

/-- `H_C ≤ K` as soon as `K` contains every letter `(x, y)` with `x ≠ y` in `C`. -/
theorem higmanVCLeafExp_H_le_of_letter {d : ℕ} {C : Finset (List (Fin d))}
    {K : Subgroup (higmanVCCommon_Q d)}
    (hK : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → higmanVCCommon_mk d (FreeGroup.of (x, y)) ∈ K) :
    higmanVCTreeNFWitPivot_H d C ≤ K := by
  intro h hh
  obtain ⟨r, rfl⟩ := higmanVCTreeNFWitPivot_mem_H.mp hh
  clear hh
  induction r using FreeGroup.induction_on with
  | C1 =>
    rw [map_one, map_one]
    exact Subgroup.one_mem _
  | of p =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    rw [higmanVCAll_iota_of]
    show higmanVCCommon_mk d (FreeGroup.of (x, y)) ∈ _
    by_cases hxy : x = y
    · subst hxy
      rw [higmanVCCommon_mk_comparable (x := x) (y := x) fun h => h.1 (List.prefix_refl x)]
      exact Subgroup.one_mem _
    · exact hK x hx y hy hxy
  | inv_of _ ih =>
    rw [map_inv, map_inv]
    exact Subgroup.inv_mem _ ih
  | mul g₁ g₂ ih₁ ih₂ =>
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ ih₁ ih₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_H_le_of_letter

/-- The pattern refinement `C ⋆ T = {c ++ e | c ∈ C, e ∈ T}`. -/
def higmanVCLeafExp_star {d : ℕ} (C T : Finset (List (Fin d))) : Finset (List (Fin d)) :=
  C.biUnion fun c => T.image fun e => c ++ e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_star

theorem higmanVCLeafExp_mem_star {d : ℕ} {C T : Finset (List (Fin d))} {x : List (Fin d)} :
    x ∈ higmanVCLeafExp_star C T ↔ ∃ c ∈ C, ∃ e ∈ T, c ++ e = x := by
  simp only [higmanVCLeafExp_star, Finset.mem_biUnion, Finset.mem_image]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_mem_star

/-- The pattern refinement of an antichain by an antichain is an antichain. -/
theorem higmanVCLeafExp_star_isAC {d : ℕ} {C T : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hT : higmanVCTreeNFWitPivot_IsAC T) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCLeafExp_star C T) := by
  intro u hu v hv huv hpre
  obtain ⟨c, hc, e, he, rfl⟩ := higmanVCLeafExp_mem_star.mp hu
  obtain ⟨c', hc', e', he', rfl⟩ := higmanVCLeafExp_mem_star.mp hv
  by_cases hcc : c = c'
  · rw [← hcc] at hpre
    have h1 : e <+: e' := (List.prefix_append_right_inj c).mp hpre
    by_cases hee : e = e'
    · exact huv (by rw [hee, hcc])
    · exact hT e he e' he' hee h1
  · have h1 : c <+: c' ++ e' := (List.prefix_append c e).trans hpre
    have h2 : c' <+: c' ++ e' := List.prefix_append c' e'
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hC c hc c' hc' hcc h
    · exact hC c' hc' c hc (Ne.symm hcc) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_star_isAC

/-- **Monotonicity under arbitrary finite pattern refinement.**  `H_C ≤ H_{C ⋆ T}` for an
antichain `C` and any tree `T`. -/
theorem higmanVCLeafExp_H_le_star {d : ℕ} {C T : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hT : higmanVCLeafExp_IsTree T) :
    higmanVCTreeNFWitPivot_H d C ≤ higmanVCTreeNFWitPivot_H d (higmanVCLeafExp_star C T) :=
  higmanVCLeafExp_H_le_of_letter fun x hx y hy hxy =>
    higmanVCLeafExp_tree_mem hT x y (hC x hx y hy hxy) (hC y hy x hx (Ne.symm hxy))
      fun e he => higmanVCLeafExp_letter_mem_H
        (higmanVCLeafExp_mem_star.mpr ⟨x, hx, e, he, rfl⟩)
        (higmanVCLeafExp_mem_star.mpr ⟨y, hy, e, he, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_H_le_star

end GroupApproximation.BooneHigman.Metabelian.Envelope
