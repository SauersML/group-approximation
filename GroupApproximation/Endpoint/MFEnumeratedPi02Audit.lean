import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Computability.MFEnumeratedPi02

/-!
# Axiom audit for the enumerated-presentation MF classification

`mfEnumeratedExactClassification` is a closed proposition: operator-MF is
`Π⁰₂`-complete and its failure `Σ⁰₂`-complete on standard recursively
enumerated presentation codes.  It is subjected to the closed-endpoint gate,
which rejects both unexpected axioms and hidden leading construction inputs.
-/

#audit_closed_axioms GroupApproximation.MFEnumeratedPi02.mfEnumeratedExactClassification
