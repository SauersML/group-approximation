import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotACReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Completing a deep antichain (lane bh-met-77u)

Notation as in `EnvelopeHigmanVCTreeNFWitPivot`: `Q = higmanVCCommon_Q d`, and `H_C` is the image
in `Q` of the antichain subgroup on `C`.

For an antichain `C` and a bound `L` at least every length in `C`,
`higmanVCPivotY_complete C L = C ∪ {w : |w| = L, no prefix of w lies in C}` has these properties.

* It is an antichain (`higmanVCPivotY_complete_isAC`).
* It keeps every lower bound on lengths up to `L` (`higmanVCPivotY_complete_length`).
* Every word of length `L` has a prefix in it (`higmanVCPivotY_complete_cover`).
* It contains `C`, so `H_C ≤ H_{C ∪ …}` (`higmanVCPivotY_H_mono`).

So in the deep pivot closure `higmanVCPivotAC_Closed` one may assume that `C` is complete.
`higmanVCPivotY_cone_cover` records what completeness buys: every short word `x` has its cone
at depth `L` tiled by elements of `C` that extend `x`.  This applies to both `x = a` and `x = b`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `H_C ≤ H_{C'}` whenever `C ⊆ C'`. -/
theorem higmanVCPivotY_H_mono {d : ℕ} {C C' : Finset (List (Fin d))} (hsub : C ⊆ C') :
    higmanVCTreeNFWitPivot_H d C ≤ higmanVCTreeNFWitPivot_H d C' := by
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
    exact higmanVCTreeNFWitPivot_mem_H.mpr
      ⟨FreeGroup.of (⟨x, hsub hx⟩, ⟨y, hsub hy⟩),
        congrArg (higmanVCCommon_mk d) (higmanVCAll_iota_of _ _)⟩
  | inv_of _ ih =>
    rw [map_inv, map_inv]
    exact Subgroup.inv_mem _ ih
  | mul g₁ g₂ ih₁ ih₂ =>
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ ih₁ ih₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_H_mono

/-- The words of length `L` with no prefix in `C`. -/
noncomputable def higmanVCPivotY_fill {d : ℕ} (C : Finset (List (Fin d))) (L : ℕ) :
    Finset (List (Fin d)) :=
  (higmanVCCentral_words d L).filter fun w => ∀ c ∈ C, ¬ c <+: w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_fill

theorem higmanVCPivotY_mem_fill {d : ℕ} {C : Finset (List (Fin d))} {L : ℕ}
    {w : List (Fin d)} :
    w ∈ higmanVCPivotY_fill C L ↔ w.length = L ∧ ∀ c ∈ C, ¬ c <+: w := by
  rw [higmanVCPivotY_fill, Finset.mem_filter, higmanVCCentral_mem_words_iff]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_mem_fill

/-- The completion `C ∪ fill C L` of `C` at depth `L`. -/
noncomputable def higmanVCPivotY_complete {d : ℕ} (C : Finset (List (Fin d))) (L : ℕ) :
    Finset (List (Fin d)) :=
  C ∪ higmanVCPivotY_fill C L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_complete

theorem higmanVCPivotY_subset_complete {d : ℕ} (C : Finset (List (Fin d))) (L : ℕ) :
    C ⊆ higmanVCPivotY_complete C L :=
  fun _ hc => Finset.mem_union_left _ hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_subset_complete

/-- The completion of an antichain at a depth `L ≥` every length is an antichain. -/
theorem higmanVCPivotY_complete_isAC {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) {L : ℕ} (hL : ∀ c ∈ C, c.length ≤ L) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCPivotY_complete C L) := by
  intro u hu v hv huv hpre
  rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
  · exact hC u hu v hv huv hpre
  · exact (higmanVCPivotY_mem_fill.mp hv).2 u hu hpre
  · obtain ⟨hlu, hnu⟩ := higmanVCPivotY_mem_fill.mp hu
    have he : u = v := hpre.eq_of_length (le_antisymm hpre.length_le ((hL v hv).trans hlu.ge))
    subst he
    exact hnu u hv (List.prefix_refl u)
  · obtain ⟨hlu, _⟩ := higmanVCPivotY_mem_fill.mp hu
    obtain ⟨hlv, _⟩ := higmanVCPivotY_mem_fill.mp hv
    exact huv (hpre.eq_of_length (hlu.trans hlv.symm))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_complete_isAC

/-- The completion keeps a lower bound `k ≤ L` on the lengths. -/
theorem higmanVCPivotY_complete_length {d : ℕ} {C : Finset (List (Fin d))} {k L : ℕ}
    (hk : ∀ c ∈ C, k ≤ c.length) (hkL : k ≤ L) :
    ∀ c ∈ higmanVCPivotY_complete C L, k ≤ c.length := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact hk c hc
  · rw [(higmanVCPivotY_mem_fill.mp hc).1]
    exact hkL

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_complete_length

/-- Every word of length `L` has a prefix in the completion at depth `L`. -/
theorem higmanVCPivotY_complete_cover {d : ℕ} (C : Finset (List (Fin d))) (L : ℕ) :
    ∀ w : List (Fin d), w.length = L → ∃ c ∈ higmanVCPivotY_complete C L, c <+: w := by
  intro w hw
  by_cases h : ∃ c ∈ C, c <+: w
  · obtain ⟨c, hc, hcw⟩ := h
    exact ⟨c, Finset.mem_union_left _ hc, hcw⟩
  · have hf : w ∈ higmanVCPivotY_fill C L :=
      higmanVCPivotY_mem_fill.mpr ⟨hw, fun c hc hcw => h ⟨c, hc, hcw⟩⟩
    exact ⟨w, Finset.mem_union_right _ hf, List.prefix_refl w⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_complete_cover

/-- **Cone tiling.**  If `C` is complete at depth `M` and every word of `C` has length `≥ k`,
then each depth-`M` word `w` in the cone of a word `x` with `|x| ≤ k` has its `C`-prefix inside
that cone. -/
theorem higmanVCPivotY_cone_cover {d k M : ℕ} {C : Finset (List (Fin d))}
    (hlen : ∀ c ∈ C, k ≤ c.length)
    (hcov : ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w)
    {x w : List (Fin d)} (hx : x.length ≤ k) (hxw : x <+: w) (hw : w.length = M) :
    ∃ c ∈ C, x <+: c ∧ c <+: w := by
  obtain ⟨c, hc, hcw⟩ := hcov w hw
  exact ⟨c, hc, List.prefix_of_prefix_length_le hxw hcw (hx.trans (hlen c hc)), hcw⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotY_cone_cover

end GroupApproximation.BooneHigman.Metabelian.Envelope
