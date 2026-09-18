import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWitPivotWit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonPush
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFConverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Deep refinement of antichain subgroups (lane bh-met-77s)

Notation as in `EnvelopeHigmanVCTreeNFWitPivot`: `Q = higmanVCCommon_Q d`, `H_C` is the image
of the antichain subgroup on `C`.

`higmanVCPivotAC_refine C j` is the antichain `{c ++ e | c ∈ C, |e| = j}`.  An antichain stays
an antichain under refinement (`higmanVCPivotAC_refine_isAC`), and `H_C ≤ H_{C_j}`
(`higmanVCPivotAC_H_le_refine`).  The proof uses deep splitting (`higmanVCCommon_mk_deep`): an
incomparable letter `(x, y)` is the product of the letters `(x e, y e)` over `|e| = j`.

This is the "depth WLOG" half of the reduction in `EnvelopeHigmanVCPivotACReduce`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The depth-`j` refinement `{c ++ e | c ∈ C, |e| = j}` of `C`. -/
def higmanVCPivotAC_refine {d : ℕ} (C : Finset (List (Fin d))) (j : ℕ) :
    Finset (List (Fin d)) :=
  C.biUnion fun c => (higmanVCCentral_words d j).image fun e => c ++ e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_refine

theorem higmanVCPivotAC_mem_refine {d : ℕ} {C : Finset (List (Fin d))} {j : ℕ}
    {x : List (Fin d)} :
    x ∈ higmanVCPivotAC_refine C j ↔ ∃ c ∈ C, ∃ e : List (Fin d), e.length = j ∧ x = c ++ e := by
  rw [higmanVCPivotAC_refine, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hx⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨c, hc, e, (higmanVCCentral_mem_words_iff d j e).mp he, rfl⟩
  · rintro ⟨c, hc, e, he, rfl⟩
    exact ⟨c, hc, Finset.mem_image.mpr ⟨e, (higmanVCCentral_mem_words_iff d j e).mpr he, rfl⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_mem_refine

/-- Every word of the depth-`j` refinement has length at least `j`. -/
theorem higmanVCPivotAC_refine_length {d : ℕ} {C : Finset (List (Fin d))} {j : ℕ}
    {x : List (Fin d)} (hx : x ∈ higmanVCPivotAC_refine C j) : j ≤ x.length := by
  obtain ⟨c, _, e, he, rfl⟩ := higmanVCPivotAC_mem_refine.mp hx
  rw [List.length_append]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_refine_length

/-- The refinement of an antichain is an antichain. -/
theorem higmanVCPivotAC_refine_isAC {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (j : ℕ) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCPivotAC_refine C j) := by
  intro u hu v hv huv hpre
  obtain ⟨c, hc, e, he, rfl⟩ := higmanVCPivotAC_mem_refine.mp hu
  obtain ⟨c', hc', e', he', rfl⟩ := higmanVCPivotAC_mem_refine.mp hv
  by_cases hcc : c = c'
  · subst hcc
    have h1 : e <+: e' := (List.prefix_append_right_inj c).mp hpre
    exact huv (congrArg (c ++ ·) (h1.eq_of_length (he.trans he'.symm)))
  · have h1 : c <+: c' ++ e' := (List.prefix_append c e).trans hpre
    have h2 : c' <+: c' ++ e' := List.prefix_append c' e'
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hC c hc c' hc' hcc h
    · exact hC c' hc' c hc (Ne.symm hcc) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_refine_isAC

/-- The `m`-fold split of `(x, y)` lies in any subgroup containing all `(x e, y e)`, `|e| = m`. -/
theorem higmanVCPivotAC_deep_mem {d : ℕ} {K : Subgroup (higmanVCCommon_Q d)} (m : ℕ) :
    ∀ x y : List (Fin d), (∀ e : List (Fin d), e.length = m →
      higmanVCCommon_mk d (FreeGroup.of (x ++ e, y ++ e)) ∈ K) →
      higmanVCCommon_mk d (higmanVCCommon_deep d m x y) ∈ K := by
  induction m with
  | zero =>
    intro x y h
    have h0 := h [] rfl
    rw [List.append_nil, List.append_nil] at h0
    rw [higmanVCCommon_deep_zero]
    exact h0
  | succ m ih =>
    intro x y h
    rw [higmanVCCommon_deep_succ, map_list_prod, List.map_map]
    refine Subgroup.list_prod_mem _ fun q hq => ?_
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
    refine ih (x ++ [a]) (y ++ [a]) fun e he => ?_
    have hl : ([a] ++ e).length = m + 1 := by
      rw [List.length_append, List.length_singleton, he, Nat.add_comm]
    have h1 := h ([a] ++ e) hl
    rwa [← List.append_assoc, ← List.append_assoc] at h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_deep_mem

/-- **Depth WLOG.**  `H_C ≤ H_{C_j}` for the depth-`j` refinement `C_j` of an antichain `C`. -/
theorem higmanVCPivotAC_H_le_refine {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (j : ℕ) :
    higmanVCTreeNFWitPivot_H d C ≤ higmanVCTreeNFWitPivot_H d (higmanVCPivotAC_refine C j) := by
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
    · have h1 : ¬ x <+: y := hC x hx y hy hxy
      have h2 : ¬ y <+: x := hC y hy x hx (Ne.symm hxy)
      rw [← higmanVCCommon_mk_deep j h1 h2]
      refine higmanVCPivotAC_deep_mem j x y fun e he => ?_
      have hxe : x ++ e ∈ higmanVCPivotAC_refine C j :=
        higmanVCPivotAC_mem_refine.mpr ⟨x, hx, e, he, rfl⟩
      have hye : y ++ e ∈ higmanVCPivotAC_refine C j :=
        higmanVCPivotAC_mem_refine.mpr ⟨y, hy, e, he, rfl⟩
      exact higmanVCTreeNFWitPivot_mem_H.mpr
        ⟨FreeGroup.of (⟨x ++ e, hxe⟩, ⟨y ++ e, hye⟩),
          congrArg (higmanVCCommon_mk d) (higmanVCAll_iota_of _ _)⟩
  | inv_of _ ih =>
    rw [map_inv, map_inv]
    exact Subgroup.inv_mem _ ih
  | mul g₁ g₂ ih₁ ih₂ =>
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ ih₁ ih₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCPivotAC_H_le_refine

end GroupApproximation.BooneHigman.Metabelian.Envelope
