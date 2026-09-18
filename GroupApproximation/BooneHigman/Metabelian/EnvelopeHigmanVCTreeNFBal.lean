import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeLevelGap
import GroupApproximation.Meta.AxiomGuard

/-!
# The balanced subgroup of all depths, and its faithfulness (lane bh-met-77l)

Write `K = normalClosure (higmanVC_rels d fun _ => True)` and `Q = higmanVCCommon_Q d`.  For
each `M` let `B_M ≤ Q` be the image of the finite symmetric group on the words of length `M`
(the range of `mk ∘ higmanVCAll_iota (higmanVCCentral_words d M)`).

**Proved here, with no hypotheses.**
* `higmanVCTreeNF_range_mono`: `B_M ≤ B_{M'}` for `M ≤ M'`.  Each generator of `B_M` is a
  balanced letter.  By `higmanVCCentral_letter_mem`, balanced letters of length `≤ M'` lie in
  `B_{M'}`.
* `higmanVCTreeNF_U`: the directed union `U = ⋃_M B_M` as a subgroup of `Q`.  It contains every
  balanced letter (`higmanVCTreeNF_letter_mem`).
* `higmanVCTreeNF_U_faithful`: `U` is faithful.  If a kernel word has class in `U`, it lies in
  `K`.  This comes from `higmanVCTreeLevel_bal_faithful`.

This file is the "balanced" half of the normal-form argument in `EnvelopeHigmanVCTreeNFSchreier`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The balanced images are monotone in the depth. -/
theorem higmanVCTreeNF_range_mono {d M M' : ℕ} (h : M ≤ M') {q : higmanVCCommon_Q d}
    (hq : q ∈
      ((higmanVCCommon_mk d).comp (higmanVCAll_iota (higmanVCCentral_words d M))).range) :
    q ∈ ((higmanVCCommon_mk d).comp (higmanVCAll_iota (higmanVCCentral_words d M'))).range := by
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hq
  clear hq
  induction r using FreeGroup.induction_on with
  | C1 =>
    rw [map_one]
    exact Subgroup.one_mem _
  | of p =>
    rw [MonoidHom.comp_apply, higmanVCAll_iota_of]
    have h1 := (higmanVCCentral_mem_words_iff d M p.1.1).mp p.1.2
    have h2 := (higmanVCCentral_mem_words_iff d M p.2.1).mp p.2.2
    exact higmanVCCentral_letter_mem (by omega) (by omega)
  | inv_of _ ih =>
    rw [map_inv]
    exact Subgroup.inv_mem _ ih
  | mul g₁ g₂ ih₁ ih₂ =>
    rw [map_mul]
    exact Subgroup.mul_mem _ ih₁ ih₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_range_mono

/-- The balanced subgroup `U = ⋃_M B_M` of `Q`: every class that is a word in balanced letters
of some common length. -/
noncomputable def higmanVCTreeNF_U (d : ℕ) : Subgroup (higmanVCCommon_Q d) where
  carrier := {q | ∃ M : ℕ,
    q ∈ ((higmanVCCommon_mk d).comp (higmanVCAll_iota (higmanVCCentral_words d M))).range}
  mul_mem' := by
    rintro q₁ q₂ ⟨M₁, h₁⟩ ⟨M₂, h₂⟩
    exact ⟨max M₁ M₂, Subgroup.mul_mem _ (higmanVCTreeNF_range_mono (le_max_left M₁ M₂) h₁)
      (higmanVCTreeNF_range_mono (le_max_right M₁ M₂) h₂)⟩
  one_mem' := ⟨0, Subgroup.one_mem _⟩
  inv_mem' := by
    rintro q ⟨M, h⟩
    exact ⟨M, Subgroup.inv_mem _ h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_U

/-- Membership in `U`. -/
theorem higmanVCTreeNF_mem_U {d : ℕ} {q : higmanVCCommon_Q d} :
    q ∈ higmanVCTreeNF_U d ↔ ∃ M : ℕ,
      q ∈ ((higmanVCCommon_mk d).comp (higmanVCAll_iota (higmanVCCentral_words d M))).range :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_mem_U

/-- Every balanced letter lies in `U`. -/
theorem higmanVCTreeNF_letter_mem {d : ℕ} {u v : List (Fin d)} (huv : u.length = v.length) :
    higmanVCCommon_mk d (FreeGroup.of (u, v)) ∈ higmanVCTreeNF_U d :=
  higmanVCTreeNF_mem_U.mpr ⟨u.length, higmanVCCentral_letter_mem huv le_rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_letter_mem

/-- **`U` is faithful.**  A kernel word whose class lies in `U` lies in `K`. -/
theorem higmanVCTreeNF_U_faithful {d : ℕ} (hd : 0 < d)
    {r : FreeGroup (List (Fin d) × List (Fin d))} (hr : r ∈ (higmanVC_evalAll d).ker)
    (hm : higmanVCCommon_mk d r ∈ higmanVCTreeNF_U d) :
    r ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
  obtain ⟨M, hM⟩ := higmanVCTreeNF_mem_U.mp hm
  exact higmanVCTreeLevel_bal_faithful hd M hr (higmanVCTreeNF_range_mono (Nat.le_succ M) hM)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_U_faithful

end GroupApproximation.BooneHigman.Metabelian.Envelope
