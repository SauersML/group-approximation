import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllAntichain
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCompleteReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Kernel of the all-swaps presentation: reduction to one antichain (lane bh-met-77c)

Target (1) of lane bh-met-77c is
`(higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True)` for
`1 < d`, i.e. the standard relators present `V_d` on all ordered pairs of words.

`EnvelopeHigmanVCAllAntichain` proves (1) unconditionally for words in the letters of one
finite antichain `C` (`higmanVCAll_antichain_mem`), using the transposition presentation of
`Equiv.Perm C` and cone tracking.  What is left is `HigmanVCAllAntichainStatement`: modulo the
standard relators, every kernel element is congruent to such a word.

**Warning: the gap is logically equivalent to (1).**  It implies (1)
(`higmanVCAll_ker_le_of_antichain`), and (1) implies it with `C = ∅`, `r' = 1`
(`higmanVCAll_antichain_of_ker_le`).  Any statement that yields (1) with nothing else supplied is
at least as strong as (1), so no gap can be strictly weaker.  This gap is strictly smaller in
**proof content only**: the vertex-group (single antichain) faithfulness is discharged here.
The rest is the groupoid/normal-form argument that moves a word across codes of mixed depth,
using the split and conjugation relators.  (1) is the standard infinite presentation of
Higman–Thompson `V_d` by transpositions of cones.  This lane believes it is true but did not
verify it.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Gap.**  Every kernel element is congruent, modulo the standard relators, to a word in the
letters of one finite antichain.  This is logically equivalent to (1); see the module
docstring. -/
def HigmanVCAllAntichainStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ r ∈ (higmanVC_evalAll d).ker, ∃ C : Finset (List (Fin d)),
    (∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) ∧ ∃ r' : FreeGroup (↥C × ↥C),
      r * (higmanVCAll_iota C r')⁻¹ ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCAllAntichainStatement

/-- **(1) from the gap.** -/
theorem higmanVCAll_ker_le_of_antichain (h : HigmanVCAllAntichainStatement) (d : ℕ)
    (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
  intro r hr
  obtain ⟨C, hC, r', hr'⟩ := h d hd r hr
  have hN : Subgroup.normalClosure (higmanVC_rels d fun _ => True) ≤
      (higmanVC_evalAll d).ker :=
    Subgroup.normalClosure_le_normal (higmanVC_rels_subset_ker d _)
  have h1 : higmanVC_evalAll d (higmanVCAll_iota C r') = 1 := by
    have h2 := hN hr'
    rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp hr, one_mul,
      inv_eq_one] at h2
    exact h2
  have h3 := higmanVCAll_antichain_mem (by omega) C hC r' h1
  have h4 := mul_mem hr' h3
  rw [inv_mul_cancel_right] at h4
  exact h4

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_ker_le_of_antichain

/-- **The gap from (1)** (with `C = ∅`): the gap is equivalent to (1), not weaker. -/
theorem higmanVCAll_antichain_of_ker_le
    (h : ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) :
    HigmanVCAllAntichainStatement := by
  intro d hd r hr
  refine ⟨∅, fun u hu => absurd hu (Finset.notMem_empty u), 1, ?_⟩
  rw [map_one, inv_one, mul_one]
  exact h d hd hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_antichain_of_ker_le

/-- **Transfer.**  The gap and part (2) of `HigmanVCTransferStatement` (the extension `τ`
killing the long relators) give `HigmanVCTransferStatement`. -/
theorem higmanVCAll_transfer_of_antichain_of_tau (hA : HigmanVCAllAntichainStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVCTransferStatement :=
  fun d hd => ⟨higmanVCAll_ker_le_of_antichain hA d hd, hB d hd⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_transfer_of_antichain_of_tau

/-- The gap and part (2) give short completeness of the finite presentation of `V_d`. -/
theorem higmanVCAll_complete_of_antichain_of_tau (hA : HigmanVCAllAntichainStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVFPShortCompleteStatement :=
  higmanVC_complete_of_transfer (higmanVCAll_transfer_of_antichain_of_tau hA hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_complete_of_antichain_of_tau

/-- The gap and part (2) give finite presentability of `V_d`. -/
theorem higmanVCAll_finFP_of_antichain_of_tau (hA : HigmanVCAllAntichainStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVFinFPStatement :=
  higmanVC_finFP_of_transfer (higmanVCAll_transfer_of_antichain_of_tau hA hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCAll_finFP_of_antichain_of_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
