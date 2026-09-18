import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3VacCaseB
import GroupApproximation.Meta.AxiomGuard

/-!
# The rest statement is vacuous (lane bh-met-92x)

`higmanVCTauFix3Vac_rest` proves `higmanVCTauFix3_RestStatement` outright: every instance
off the cross, one-fixed and both-fixed families has a flexible option at `(x, y)`,
contradicting the negated hypotheses.

* `|p| = |q|`: flexible A (`higmanVCTauFix3Vac_flexA`);
* `|p| ≠ |q|`: flexible B (`higmanVCTauFix3Vac_flexB`).

Then `higmanVCTauFix3Vac_tau : HigmanVCTauStatement` follows through
`higmanVCTauFix3_tau_of_fix3`.

No ConjShort, ShortComplete, TFPShortComplete, CentralBalanced or AllAntichain; no witness
`X = Q`, `c = id`; no Higman presentation; no `Q ≅ V_d`; no literature input.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Vacuity of the rest statement.** -/
theorem higmanVCTauFix3Vac_rest : higmanVCTauFix3_RestStatement := by
  intro d hd n p q x y x' y' hpq hqp hC hC' hF hF' hB hp hq hx hx' hs _ _ _ hFA hFB _ _ hmx
    hmy hxy hyx _ _
  have hd' : 1 < d := by omega
  by_cases hl : p.length = q.length
  · exact absurd (higmanVCTauFix3Vac_flexA hd' hpq hqp hl hp hq hs hmx hmy hxy hyx hB hF hF')
      hFA
  · exact absurd (higmanVCTauFix3Vac_flexB hd' hpq hqp hl hp hq hC hC' (by omega) hs hmx hmy
      hxy hyx) hFB

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_rest

/-- **The statement `HigmanVCTauStatement`**, through the vacuity of the rest statement. -/
theorem higmanVCTauFix3Vac_tau : HigmanVCTauStatement :=
  higmanVCTauFix3_tau_of_fix3 higmanVCTauFix3Vac_rest

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
