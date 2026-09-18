import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCompleteBase
import GroupApproximation.Meta.AxiomGuard

/-!
# Reducing `HigmanVFPShortCompleteStatement` to a transfer statement (lane bh-met-77b)

**THE TARGET `HigmanVFPShortCompleteStatement` IS NOT PROVED HERE.**  It is reduced to the
single remaining gap `HigmanVCTransferStatement` (`higmanVC_complete_of_transfer`), which has two
conjuncts for each `d ≥ 2`:

1. **(completeness of the all-swaps presentation)** the kernel of `higmanVC_evalAll d` is the
   normal closure of the standard relators `higmanVC_rels d (fun _ => True)` (comparable letters,
   involutions, conjugations, splits of all lengths);
2. **(long swaps in the short quotient)** there are values `τ p ∈ higmanVC_Q d` for the pairs
   `p` with a word of length `≥ 4` such that `ψ_τ` kills every standard relator that involves
   such a word.

Route of the reduction.  A short kernel element `r` includes to `ι r` in the all-swaps kernel
(`higmanVC_evalAll_comp_iota`), hence into the normal closure of the standard relators (1).
Every standard relator is killed by `ψ_τ`: the short ones by `higmanVC_psi_short` (for every
`τ`), the others by (2).  So `ψ_τ (ι r) = 1`, and `ψ_τ ∘ ι` is the quotient map
(`higmanVC_psi_comp_iota`); thus `r` lies in the normal closure of `higmanVFPRelators d`.

Why the gap is strictly smaller in proof content: the standard proof of the target is exactly
(1) + (2) + this reduction.  The reduction and the base case of (2) (standard relators among
words of length `≤ 3`) are proved here.  Soundness of the relators is `higmanVC_rels_subset_ker`.

Truth.  (1) is the classical infinite presentation of `V_d` by cone swaps: every kernel word is
refined by splits to transpositions of the leaves of one complete prefix code and then reduced by
the Coxeter relations of the symmetric group on those leaves, which are conjugation and involution
relators.  (2) is true whenever the target is true: take `τ p` a preimage of `vgenSwapOrOne p`
under the then-injective map `higmanVC_Q d → V_d`; then `ψ_τ` factors through `higmanVC_evalAll d`,
which kills the standard relators.  Neither conjunct is verified here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The combination step**, for one `d ≥ 1`. -/
theorem higmanVC_complete_of_parts {d : ℕ} (hd : 0 < d)
    (hA : (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True))
    (τ : List (Fin d) × List (Fin d) → higmanVC_Q d)
    (hB : ∀ t ∈ higmanVC_rels d (fun _ => True),
      t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    (FreeGroup.lift (vgenShortSwaps (Fin d))).ker ≤
      Subgroup.normalClosure (higmanVFPRelators d) := by
  intro r hr
  have h1 : higmanVC_iota d r ∈ (higmanVC_evalAll d).ker := by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, higmanVC_evalAll_comp_iota]
    exact MonoidHom.mem_ker.mp hr
  have h2 : Subgroup.normalClosure (higmanVC_rels d fun _ => True) ≤ (higmanVC_psi d τ).ker :=
    Subgroup.normalClosure_le_normal fun t ht => by
      by_cases hs : t ∈ higmanVC_rels d (fun l => l.length ≤ 3)
      · exact MonoidHom.mem_ker.mpr (higmanVC_psi_short τ hd hs)
      · exact MonoidHom.mem_ker.mpr (hB t ht hs)
  have h3 : higmanVC_mk d r = 1 := by
    rw [← higmanVC_psi_comp_iota d τ, MonoidHom.comp_apply]
    exact MonoidHom.mem_ker.mp (h2 (hA h1))
  exact higmanVC_mem_of_mk h3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_complete_of_parts

/-- **THE REMAINING GAP (lane bh-met-77b).**  For every `d ≥ 2`: (1) the all-swaps standard
presentation of `V_d` is complete, and (2) the long cone swaps have values in the short quotient
`higmanVC_Q d` under which every standard relator involving a word of length `≥ 4` holds.  See the
module docstring for why this is strictly smaller in proof content than
`HigmanVFPShortCompleteStatement` and why it is believed true; it is not verified. -/
def HigmanVCTransferStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) ∧
      ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
        ∀ t ∈ higmanVC_rels d (fun _ => True),
          t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTransferStatement

/-- **Endpoint.**  The transfer gap implies the explicit-length Higman statement. -/
theorem higmanVC_complete_of_transfer (h : HigmanVCTransferStatement) :
    HigmanVFPShortCompleteStatement := by
  intro d hd
  obtain ⟨hA, τ, hB⟩ := h d hd
  exact higmanVC_complete_of_parts (by omega) hA τ hB

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_complete_of_transfer

/-- **Endpoint.**  The transfer gap implies that `V_d` is finitely presented for `d ≥ 2`. -/
theorem higmanVC_finFP_of_transfer (h : HigmanVCTransferStatement) : HigmanVFinFPStatement :=
  higmanVFP_finFP_of_complete (higmanVC_complete_of_transfer h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_finFP_of_transfer

end GroupApproximation.BooneHigman.Metabelian.Envelope
