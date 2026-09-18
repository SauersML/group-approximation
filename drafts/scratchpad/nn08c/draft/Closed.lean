import GroupApproximation.Manuscript.NonMFNotes.Full.FFExistencePrinted.Assembly
import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms
import GroupApproximation.Manuscript.NonMF.TheoremCAssembly
import GroupApproximation.Kazhdan.KotowskiOllivierClosed
import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# `rem:ff-realization`, first sentence: closed existence

Manuscript `non_mf_group_notes.tex`, Remark `rem:ff-realization` (l.2818):
"The construction of [FFF, §2] gives a finitely presented torsion-free
property-(T) group `P` containing `P₁ × P₂ × S` ..."

The three steps of [FFF, §2] are all closed:

* `H₀` is `Hyperbolic.sharpExistence_closed` (Kotowski-Ollivier).
* `U` is `Manuscript.NonMF.TheoremC.chiodo` (Chiodo, Theorem 3.10).
* `P` comes from
  `TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger`,
  applied to Osin's relative Greendlinger lemma
  `Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_zero`.

The rest is `Full/FFExistencePrinted/Assembly.lean`.
-/

namespace GroupApproximation.Full.NN08c

universe w

/-- **`rem:ff-realization`, first sentence as printed** (`non_mf_group_notes.tex`
l.2818; [FFF, §2]). -/
theorem ffPrintedExistence : NN08b.FFPrintedExistenceStatement.{w} := by
  obtain ⟨H₀, _, hinf, hfp, htf, hhyp, hT⟩ := Hyperbolic.sharpExistence_closed
  obtain ⟨U, _, hUfp, hUtf, hUniv⟩ := Manuscript.NonMF.TheoremC.chiodo
  obtain ⟨P, _, hPfp, hPtf, ⟨p, hp⟩, ⟨e, he⟩⟩ :=
    Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger
      GL06.relativeGreendlingerQuasiGeodesicLeastArea_zero H₀ U inferInstance inferInstance
      hinf hfp htf hhyp hT hUfp hUtf
  exact ffPrintedExistence_of_smallCancellationQuotient hT hUniv hPfp hPtf p hp e he

/-- **`rem:ff-realization`, the existence consumed by `NN08.remFFRealization`**
(`non_mf_group_notes.tex` l.2818). -/
theorem ffMinimalExistence : NN08b.FFMinimalExistenceStatement.{w} := by
  obtain ⟨H₀, _, hinf, hfp, htf, hhyp, hT⟩ := Hyperbolic.sharpExistence_closed
  obtain ⟨U, _, hUfp, hUtf, hUniv⟩ := Manuscript.NonMF.TheoremC.chiodo
  obtain ⟨P, _, hPfp, hPtf, ⟨p, hp⟩, ⟨e, he⟩⟩ :=
    Manuscript.NonMF.TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger
      GL06.relativeGreendlingerQuasiGeodesicLeastArea_zero H₀ U inferInstance inferInstance
      hinf hfp htf hhyp hT hUfp hUtf
  exact ffMinimalExistence_of_smallCancellationQuotient hT hUniv hPfp hPtf p hp e he

end GroupApproximation.Full.NN08c

#audit_closed_axioms GroupApproximation.Full.NN08c.ffPrintedExistence
#audit_closed_axioms GroupApproximation.Full.NN08c.ffMinimalExistence
