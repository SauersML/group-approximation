import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCStepBCore
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Step B, part 3: the core residual gives letter-closure of `S`, hence Higman (1)
(lane bh-met-93f)

Notation as in `EnvelopeHigmanVCStepBClosed`.

**Proved here, from `HigmanVCStepBCoreStatement` only.**
* `higmanVCStepB_closed_of_core`: the core residual gives `higmanVCStepB_Closed d`.
  Take `s = u₁ h u₂ ∈ S` and a letter `ℓ = mk (of (x, y))`.
  * If `x` and `y` are comparable, then `ℓ = 1`.
  * Otherwise write `u₂ = mk g` and let `N` be a push threshold for `g`.  Choose `L` bounding
    `C`.  `ℓ` lies in `H` of the depth-`(L + 1 + N)` refinement of `{x, y}`.
  * Conjugation by the pushing word (`higmanVCPivotAC_conj_mem`) then gives
    `ℓ' = u₂ ℓ u₂⁻¹ ∈ H_D`, with every word of `D` of length `≥ L + 1`.
  * Replace `C` by its completion `C'` at depth `L`.  This is a complete code, and `D`
    strictly refines it.
  * `higmanVCStepB_core_full` gives `h ℓ' ∈ S`.  Then `s ℓ = u₁ (h ℓ') u₂ ∈ S`.
* `higmanVCStepB_ker_le_of_core` and `higmanVCStepB_antichain_of_core`: the endpoints.

**LOUD: Higman (1) is proved here only conditionally**, on the combinatorial core residual.
See `EnvelopeHigmanVCStepBCore` for its status.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The core residual gives letter-closure of `S`. -/
theorem higmanVCStepB_closed_of_core (hK : HigmanVCStepBCoreStatement) {d : ℕ} (hd : 1 < d) :
    higmanVCStepB_Closed d := by
  intro s hs x y
  by_cases hxy : ¬ x <+: y ∧ ¬ y <+: x
  swap
  · rw [higmanVCCommon_mk_comparable hxy, mul_one]
    exact hs
  obtain ⟨hxy1, hxy2⟩ := hxy
  obtain ⟨u₁, hu₁, C, hC, h, hh, u₂, hu₂, rfl⟩ := higmanVCTreeNFWitPivot_mem_S.mp hs
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d u₂
  obtain ⟨N, hN⟩ := higmanVCCommon_push hd g
  obtain ⟨L, hL⟩ : ∃ L : ℕ, ∀ c ∈ C, c.length ≤ L :=
    ⟨C.sup List.length, fun c hc => Finset.le_sup (f := List.length) hc⟩
  have hxyAC := higmanVCStepB_pair_isAC hxy1 hxy2
  have hR := higmanVCPivotAC_refine_isAC hxyAC (L + 1 + N)
  have hℓ : higmanVCCommon_mk d (FreeGroup.of (x, y)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCPivotAC_refine {x, y} (L + 1 + N)) :=
    higmanVCPivotAC_H_le_refine hxyAC (L + 1 + N)
      (higmanVCLeafExp_letter_mem_H (Finset.mem_insert_self x {y})
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
  have hP := higmanVCPivotAC_conj_mem (B := L + 1) hd hN hR
    (fun _ hc => higmanVCPivotAC_refine_length hc) hℓ
  obtain ⟨D, hDdef⟩ : ∃ D : Finset (List (Fin d)),
      D = higmanVCPivotAC_push d (L + 1) g (higmanVCPivotAC_refine {x, y} (L + 1 + N)) :=
    ⟨_, rfl⟩
  rw [← hDdef] at hP
  have hD : higmanVCTreeNFWitPivot_IsAC D := by
    rw [hDdef]
    exact higmanVCPivotAC_push_isAC hd g hR
  have hDlen : ∀ z ∈ D, L + 1 ≤ z.length := by
    intro z hz
    rw [hDdef] at hz
    exact higmanVCPivotAC_push_length hd hz
  have hC'L : ∀ c ∈ higmanVCPivotY_complete C L, c.length ≤ L := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hL c hc
    · exact (higmanVCPivotY_mem_fill.mp hc).1.le
  have href : ∀ z ∈ D, ∃ c ∈ higmanVCPivotY_complete C L, c <+: z := by
    intro z hz
    have hz' := hDlen z hz
    obtain ⟨c, hc, hcw⟩ := higmanVCPivotY_complete_cover C L (z.take L)
      (List.length_take_of_le (by omega))
    exact ⟨c, hc, hcw.trans (List.take_prefix L z)⟩
  have hdeep : ∀ z ∈ D, ∀ c ∈ higmanVCPivotY_complete C L, c.length < z.length := by
    intro z hz c hc
    have h1 := hDlen z hz
    have h2 := hC'L c hc
    omega
  have key := higmanVCStepB_core_full hK hd (higmanVCPivotY_complete_isAC hC hL)
    ⟨L, hC'L, higmanVCPivotY_complete_cover C L⟩ hD href hdeep
    (higmanVCPivotY_H_mono (higmanVCPivotY_subset_complete C L) hh) hP
  have e : ∀ a b c k : higmanVCCommon_Q d, a * b * c * k = a * (b * (c * k * c⁻¹)) * c := by
    intro a b c k
    group
  rw [e]
  exact higmanVCTreeNFWitPivot_S_mul_U (higmanVCPivotAC_U_mul_S hu₁ key) hu₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_closed_of_core

/-- The core residual gives Higman's kernel inclusion at every arity `d > 1`. -/
theorem higmanVCStepB_ker_le_of_core (hK : HigmanVCStepBCoreStatement) {d : ℕ} (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCStepB_ker_le_of_closed hd (higmanVCStepB_closed_of_core hK hd)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_ker_le_of_core

/-- **Endpoint.**  The core residual gives `HigmanVCAllAntichainStatement`. -/
theorem higmanVCStepB_antichain_of_core (hK : HigmanVCStepBCoreStatement) :
    HigmanVCAllAntichainStatement :=
  higmanVCStepB_antichain_of_closed fun _ hd => higmanVCStepB_closed_of_core hK hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCStepB_antichain_of_core

end GroupApproximation.BooneHigman.Metabelian.Envelope
