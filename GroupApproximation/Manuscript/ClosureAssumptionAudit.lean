import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.OneSidedMFRadical.RadicalCalculusSentences
import GroupApproximation.Manuscript.MFRecognition.RegularRealizationSentences

/-!
# Assumption audit for closed manuscript infrastructure

The two endpoints below previously accepted the cited permanence results as
arguments.  They now invoke the corresponding proved theorems directly.
-/

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedResidualCalculusProofCurrent
#audit_axioms GroupApproximation.Manuscript.MFRecognition.Sentences.reducedProduct_separableSubalgebra_isMF_sentence

