import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWitPivot
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFSchreier
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllAntichain
import GroupApproximation.Meta.AxiomGuard

/-!
# Single-leaf expansion: the literal lemma is FALSE (lane bh-met-77w)

Notation as in `EnvelopeHigmanVCTreeNFWitPivot`: `Q = higmanVCCommon_Q d`, `H_C` is the
image of the antichain subgroup on `C`.

`higmanVCLeafExp_expand C c = (C \ {c}) ∪ {c i | i : Fin d}` is the single-leaf expansion.
It keeps antichains antichains (`higmanVCLeafExp_expand_isAC`).

**Truth check (loud).**  The single-leaf monotonicity `H_C ≤ H_{C'}` is FALSE for `d ≥ 2`
whenever `C` has a second leaf `v ≠ c`.  The letter `(c, v) ∈ H_C` evaluates in `V_d` to
the cone swap of `c` and `v`, which moves the cone at `v ∈ C'` onto the cone at `c`.  But by
cone tracking (`higmanVCAll_mapsCone_word`), every element of `H_{C'}` moves the cone at
`v ∈ C'` onto the cone at some leaf of `C'`, and `c ∉ C'`.  See
`higmanVCLeafExp_letter_not_mem`, `higmanVCLeafExp_not_le` and the concrete instance
`higmanVCLeafExp_single_leaf_false`.  The argument only uses the evaluation `Q → V_d`, so
it does not assume that Higman's relations are complete.

The correct form is refinement by one pattern (`EnvelopeHigmanVCLeafExpTree`): if every
leaf is expanded by the same finite tree `T`, then `H_C ≤ H_{C ⋆ T}`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The single-leaf expansion `(C \ {c}) ∪ {c ++ [i] | i : Fin d}`. -/
def higmanVCLeafExp_expand {d : ℕ} (C : Finset (List (Fin d))) (c : List (Fin d)) :
    Finset (List (Fin d)) :=
  C.erase c ∪ (Finset.univ : Finset (Fin d)).image fun i => c ++ [i]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_expand

theorem higmanVCLeafExp_mem_expand {d : ℕ} {C : Finset (List (Fin d))} {c x : List (Fin d)} :
    x ∈ higmanVCLeafExp_expand C c ↔ (x ≠ c ∧ x ∈ C) ∨ ∃ i : Fin d, c ++ [i] = x := by
  simp only [higmanVCLeafExp_expand, Finset.mem_union, Finset.mem_erase, Finset.mem_image,
    Finset.mem_univ, true_and]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_mem_expand

/-- The expanded leaf is gone. -/
theorem higmanVCLeafExp_not_mem_expand {d : ℕ} (C : Finset (List (Fin d))) (c : List (Fin d)) :
    c ∉ higmanVCLeafExp_expand C c := by
  intro h
  rcases higmanVCLeafExp_mem_expand.mp h with ⟨hne, _⟩ | ⟨i, hi⟩
  · exact hne rfl
  · have hl := congrArg List.length hi
    rw [List.length_append, List.length_singleton] at hl
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_not_mem_expand

theorem higmanVCLeafExp_mem_expand_of_ne {d : ℕ} {C : Finset (List (Fin d))}
    {c x : List (Fin d)} (hx : x ∈ C) (hxc : x ≠ c) : x ∈ higmanVCLeafExp_expand C c :=
  higmanVCLeafExp_mem_expand.mpr (Or.inl ⟨hxc, hx⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_mem_expand_of_ne

theorem higmanVCLeafExp_child_mem {d : ℕ} (C : Finset (List (Fin d))) (c : List (Fin d))
    (i : Fin d) : c ++ [i] ∈ higmanVCLeafExp_expand C c :=
  higmanVCLeafExp_mem_expand.mpr (Or.inr ⟨i, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_child_mem

/-- A single-leaf expansion of an antichain at one of its leaves is an antichain. -/
theorem higmanVCLeafExp_expand_isAC {d : ℕ} {C : Finset (List (Fin d))} {c : List (Fin d)}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hc : c ∈ C) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCLeafExp_expand C c) := by
  intro u hu v hv huv hpre
  rcases higmanVCLeafExp_mem_expand.mp hu with ⟨huc, huC⟩ | ⟨i, rfl⟩
  · rcases higmanVCLeafExp_mem_expand.mp hv with ⟨_, hvC⟩ | ⟨j, rfl⟩
    · exact hC u huC v hvC huv hpre
    · rcases List.prefix_concat_iff.mp hpre with h | h
      · exact huv h
      · exact hC u huC c hc huc h
  · rcases higmanVCLeafExp_mem_expand.mp hv with ⟨hvc, hvC⟩ | ⟨j, rfl⟩
    · exact hC c hc v hvC (Ne.symm hvc) ((List.prefix_append c [i]).trans hpre)
    · exact huv (congrArg (c ++ ·)
        (((List.prefix_append_right_inj c).mp hpre).eq_of_length rfl))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_expand_isAC

/-- A letter on two leaves of `C` lies in `H_C`. -/
theorem higmanVCLeafExp_letter_mem_H {d : ℕ} {C : Finset (List (Fin d))} {u v : List (Fin d)}
    (hu : u ∈ C) (hv : v ∈ C) :
    higmanVCCommon_mk d (FreeGroup.of (u, v)) ∈ higmanVCTreeNFWitPivot_H d C :=
  higmanVCTreeNFWitPivot_mem_H.mpr ⟨FreeGroup.of (⟨u, hu⟩, ⟨v, hv⟩),
    congrArg (higmanVCCommon_mk d) (higmanVCAll_iota_of _ _)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_letter_mem_H
