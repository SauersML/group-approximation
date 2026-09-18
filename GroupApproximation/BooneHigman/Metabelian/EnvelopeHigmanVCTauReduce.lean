import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFamilies
import GroupApproximation.Meta.AxiomGuard

/-!
# Reducing the `τ` part of the transfer to the conjugation and split families (bh-met-77e)

`HigmanVCTauStatement` is hypothesis `hB` of the endpoints
`higmanVCAll_{transfer,complete,finFP}_of_antichain_of_tau`: for every `d > 1` some
`τ` makes `ψ_τ` kill every standard relator of `higmanVC_rels d (fun _ => True)` that is not
all-short.

**Remaining gap.** `HigmanVCTauConjSplitStatement`: for the *canonical* `τ := higmanVCTau_tau d`
(cone-swap descent, module `EnvelopeHigmanVCTauVal`), `ψ_τ` kills every conjugation relator
and every split relator.  `higmanVCTau_of_conjSplit` proves `HigmanVCTauConjSplitStatement →
HigmanVCTauStatement`: the witness is the canonical `τ`, and the comparable and involution
families are discharged (`higmanVCTau_psi_comparable`, `higmanVCTau_psi_sq`).

**Strength (loud).** The gap is *not* weaker in logical form: it fixes `τ`, so it implies
`HigmanVCTauStatement`, and the converse is not claimed.  It is *strictly smaller in proof
content*: the existential witness `τ` is constructed and two of the four relator families
are proved for it; only the conjugation and split families remain.  Its all-short instances
already hold (`higmanVC_psi_short`), so its content is the instances with a word of length
`≥ 4`.

**Truth.** The gap follows from `HigmanVFPShortCompleteStatement` (Higman's finite
presentation of `V_d` by the short relators, the target of this chain) together with the
descent facts listed in `EnvelopeHigmanVCTauVal`: then the evaluation `higmanVC_Q d → V_d` is
injective, and by `vgen_conj_coneSwap` the canonical value of every pair evaluates to
`vgenSwapOrOne`, so `ψ_τ` of any relator evaluates to `higmanVC_evalAll` of it, which is `1`
(`higmanVC_rels_subset_ker`).  The descent facts were machine-checked (`d = 2, 3`, all words
of length `≤ 6`, 1196244 incomparable pairs, 0 failures): at each step `P`, `Q` are short and
incomparable, `(P Q)` maps the cones of the descended pair onto those of the pair, the
descended pair is incomparable, and the fuel `|v| + |w| + 1` never runs out.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Hypothesis `hB` of `higmanVCAll_transfer_of_antichain_of_tau` (part (2) of
`HigmanVCTransferStatement`). -/
def HigmanVCTauStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
    ∀ t ∈ higmanVC_rels d (fun _ => True),
      t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauStatement

/-- **Remaining gap.**  For the canonical `τ`, `ψ_τ` kills every conjugation relator and every
split relator (of words of any length). -/
def HigmanVCTauConjSplitStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    (∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVC_psi d (higmanVCTau_tau d)
        (FreeGroup.of (p, q) * FreeGroup.of (x, y) * (FreeGroup.of (p, q))⁻¹ *
          (FreeGroup.of (x', y'))⁻¹) = 1) ∧
    ∀ v w : List (Fin d), ¬ v <+: w → ¬ w <+: v →
      higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (v, w) * (higmanVC_splitAll v w)⁻¹) = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauConjSplitStatement

/-- **Reduction.**  The conjugation and split families for the canonical `τ` give `hB`. -/
theorem higmanVCTau_of_conjSplit (h : HigmanVCTauConjSplitStatement) :
    HigmanVCTauStatement := by
  intro d hd
  refine ⟨higmanVCTau_tau d, fun t ht _ => ?_⟩
  rcases ht with ⟨v, w, _, _, hc, rfl⟩ | ⟨v, w, _, _, rfl⟩ |
      ⟨p, q, x, y, x', y', _, _, _, _, _, _, hpq, hqp, hmx, hmy, hxy, hyx, hxy', hyx', rfl⟩ |
      ⟨v, w, _, _, _, h1, h2, rfl⟩
  · exact higmanVCTau_psi_comparable d hc
  · exact higmanVCTau_psi_sq d v w
  · exact (h d hd).1 p q x y x' y' hpq hqp hmx hmy hxy hyx hxy' hyx'
  · exact (h d hd).2 v w h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_of_conjSplit

/-- The transfer statement from the antichain part and the remaining gap. -/
theorem higmanVCTau_transfer_of_antichain_of_conjSplit (hA : HigmanVCAllAntichainStatement)
    (hC : HigmanVCTauConjSplitStatement) : HigmanVCTransferStatement :=
  higmanVCAll_transfer_of_antichain_of_tau hA (higmanVCTau_of_conjSplit hC)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_transfer_of_antichain_of_conjSplit

/-- Short completeness from the antichain part and the remaining gap. -/
theorem higmanVCTau_complete_of_antichain_of_conjSplit (hA : HigmanVCAllAntichainStatement)
    (hC : HigmanVCTauConjSplitStatement) : HigmanVFPShortCompleteStatement :=
  higmanVCAll_complete_of_antichain_of_tau hA (higmanVCTau_of_conjSplit hC)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_complete_of_antichain_of_conjSplit

/-- Finite presentability of `V_d` from the antichain part and the remaining gap. -/
theorem higmanVCTau_finFP_of_antichain_of_conjSplit (hA : HigmanVCAllAntichainStatement)
    (hC : HigmanVCTauConjSplitStatement) : HigmanVFinFPStatement :=
  higmanVCAll_finFP_of_antichain_of_tau hA (higmanVCTau_of_conjSplit hC)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_finFP_of_antichain_of_conjSplit

end GroupApproximation.BooneHigman.Metabelian.Envelope
