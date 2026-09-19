import GroupApproximation.BooneHigman.Join.BaseAdj

/-!
# The fundamental expansion lemma (lane bh-pal-met-join)

`FELAt T σ d`: the element `σ` of the antichain subgroup of the leaves of `T` can be rewritten
as `f · ρ`, where
* `f ∈ Phi`;
* `ρ` lies in the antichain subgroup of the leaves of `T` with the leaf `d` split;
* for some leaf `d'`, `f` carries the leaves of `T` with `d` split rigidly onto the leaves of
  `T` with `d'` split.

`fel`: every `σ ∈ jH 2 (lset T)` has `FELAt T σ d` at every leaf `d`.

Proof, by induction on `T`:
* `FELAt` is multiplicative (`felAt_mul`): conjugate the second `ρ` back through `f` (`rcl_H`).
* A letter of `node l r` joins two leaves.  If both are on the same side, it is a prefix image
  (`felAt_phi_zero`, `felAt_phi_one`, the induction hypothesis).  If they are on opposite sides,
  it is conjugate to the crossing letter `ℓ(0 1^a, 1 0^b)` by same-side letters.  For the
  crossing letter, `FELAt` is the base identity `baseR_adj` (`felAt_cross_left`,
  `felAt_cross_right`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

open BTree

/-- The expansion property of `σ` at the leaf `d` of `T`. -/
def FELAt (T : BTree) (σ : higmanVCCommon_Q 2) (d : List (Fin 2)) : Prop :=
  ∃ d' ∈ T.leaves, ∃ f ∈ Phi, ∃ ρ ∈ jH 2 (T.expand d).lset, σ = f * ρ ∧
    ∀ c' ∈ (T.expand d').leaves, ∃ c ∈ (T.expand d).leaves, MapsCone (jperm 2 f) c c'

#audit_axioms GroupApproximation.BooneHigman.Join.FELAt

theorem felAt_of_mem {T : BTree} {σ : higmanVCCommon_Q 2} {d : List (Fin 2)}
    (hd : d ∈ T.leaves) (hσ : σ ∈ jH 2 (T.expand d).lset) : FELAt T σ d :=
  ⟨d, hd, 1, Phi.one_mem, σ, hσ, (one_mul σ).symm, fun c' hc' => ⟨c', hc', by
    rw [jperm_one]; exact mapsCone_one c'⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_of_mem

theorem expand_isAC (T : BTree) (d : List (Fin 2)) : IsAC (T.expand d).lset := lset_isAC _

#audit_axioms GroupApproximation.BooneHigman.Join.expand_isAC

/-- **Multiplicativity.** -/
theorem felAt_mul {T : BTree} {σ₁ σ₂ : higmanVCCommon_Q 2} {d : List (Fin 2)}
    (h₂ : FELAt T σ₂ d) (h₁ : ∀ e ∈ T.leaves, FELAt T σ₁ e) : FELAt T (σ₁ * σ₂) d := by
  obtain ⟨d', hd', f₂, hf₂, ρ₂, hρ₂, e₂, hm₂⟩ := h₂
  obtain ⟨d'', hd'', f₁, hf₁, ρ₁, hρ₁, e₁, hm₁⟩ := h₁ d' hd'
  refine ⟨d'', hd'', f₁ * f₂, Phi.mul_mem hf₁ hf₂, f₂⁻¹ * ρ₁ * f₂ * ρ₂, ?_, ?_, ?_⟩
  · refine (jH 2 _).mul_mem ?_ hρ₂
    have h := rcl_H jd2 (expand_isAC T d') f₂⁻¹ (C' := (T.expand d).lset) ?_ hρ₁
    · rwa [inv_inv] at h
    · intro c hc
      obtain ⟨c₀, hc₀, hm⟩ := hm₂ c (mem_lset.mp hc)
      exact ⟨c₀, mem_lset.mpr hc₀, mc_inv hm⟩
  · rw [e₁, e₂]
    group
  · intro c'' hc''
    obtain ⟨c', hc', hm'⟩ := hm₁ c'' hc''
    obtain ⟨c, hc, hm⟩ := hm₂ c' hc'
    exact ⟨c, hc, mc_mul hm hm'⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_mul

theorem mem_lset_expand {T : BTree} {w : List (Fin 2)} (hw : w ∈ T.leaves) {c : List (Fin 2)} :
    c ∈ (T.expand w).lset ↔ (c ∈ T.leaves ∧ c ≠ w) ∨ c = w ++ [0] ∨ c = w ++ [1] := by
  rw [mem_lset]
  exact mem_leaves_expand T hw c

#audit_axioms GroupApproximation.BooneHigman.Join.mem_lset_expand

/-- The prefix image of `FELAt`, on the left subtree. -/
theorem felAt_phi_zero {l r : BTree} {σ : higmanVCCommon_Q 2} {d : List (Fin 2)}
    (h : FELAt l σ d) : FELAt (node l r) (jPhi 2 [0] σ) (0 :: d) := by
  obtain ⟨d', hd', f, hf, ρ, hρ, e, hm⟩ := h
  refine ⟨0 :: d', mem_leaves_node.mpr (Or.inl ⟨d', hd', rfl⟩), jPhi 2 [0] f,
    jPhi_mem_Phi [0] hf, jPhi 2 [0] ρ, ?_, by rw [e, map_mul], ?_⟩
  · refine jH_mono ?_ (jPhi_mem_jH [0] hρ)
    intro c hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    rw [expand_node_zero, mem_lset, mem_leaves_node]
    exact Or.inl ⟨c', mem_lset.mp hc', rfl⟩
  · intro c'' hc''
    rw [expand_node_zero, mem_leaves_node] at hc''
    rcases hc'' with ⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩
    · obtain ⟨c, hc, hmc⟩ := hm c' hc'
      refine ⟨0 :: c, ?_, mc_phi [0] hmc⟩
      rw [expand_node_zero, mem_leaves_node]
      exact Or.inl ⟨c, hc, rfl⟩
    · refine ⟨1 :: c', ?_, mc_phi_fix [0] f (nprefix_zero_one _ _) (nprefix_one_zero _ _)⟩
      rw [expand_node_zero, mem_leaves_node]
      exact Or.inr ⟨c', hc', rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_phi_zero

/-- The prefix image of `FELAt`, on the right subtree. -/
theorem felAt_phi_one {l r : BTree} {σ : higmanVCCommon_Q 2} {d : List (Fin 2)}
    (h : FELAt r σ d) : FELAt (node l r) (jPhi 2 [1] σ) (1 :: d) := by
  obtain ⟨d', hd', f, hf, ρ, hρ, e, hm⟩ := h
  refine ⟨1 :: d', mem_leaves_node.mpr (Or.inr ⟨d', hd', rfl⟩), jPhi 2 [1] f,
    jPhi_mem_Phi [1] hf, jPhi 2 [1] ρ, ?_, by rw [e, map_mul], ?_⟩
  · refine jH_mono ?_ (jPhi_mem_jH [1] hρ)
    intro c hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    rw [expand_node_one, mem_lset, mem_leaves_node]
    exact Or.inr ⟨c', mem_lset.mp hc', rfl⟩
  · intro c'' hc''
    rw [expand_node_one, mem_leaves_node] at hc''
    rcases hc'' with ⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩
    · refine ⟨0 :: c', ?_, mc_phi_fix [1] f (nprefix_one_zero _ _) (nprefix_zero_one _ _)⟩
      rw [expand_node_one, mem_leaves_node]
      exact Or.inl ⟨c', hc', rfl⟩
    · obtain ⟨c, hc, hmc⟩ := hm c' hc'
      refine ⟨1 :: c, ?_, mc_phi [1] hmc⟩
      rw [expand_node_one, mem_leaves_node]
      exact Or.inr ⟨c, hc, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_phi_one

end GroupApproximation.BooneHigman.Join
