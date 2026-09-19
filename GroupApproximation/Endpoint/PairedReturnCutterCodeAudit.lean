import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Higman.PairedReturnCutterCode

/-!
# Closed audit for the fixed paired-return code leaf

This roster records exactly the hypothesis-free code-level facts supplied by
the fixed paired-return cutter package.  It does not claim that the subsequent
varying Transport/Omega compiler has already been assembled.
-/

#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.evalRaw_surjective
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.fiveWords_map_evalRaw
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.closure_evalRaw_fiveWords
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.computable_ambientCode
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.computable_fiveWords
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.evalPRaw_surjective
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.pGeneratorWords_map_evalPRaw
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.ambientPGeneratorWords_map_evalRaw
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.computable_pCode
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.computable_pGeneratorWords
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.computable_ambientPGeneratorWords
#audit_closed_axioms
  GroupApproximation.Higman.PairedReturnCutterCode.computable_pMarkedWords
