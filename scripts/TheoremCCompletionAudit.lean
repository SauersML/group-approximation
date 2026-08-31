import GroupApproximation.Manuscript.NonMF.TheoremCDebts
import GroupApproximation.Meta.AxiomGuard

/-!
# Kernel completion gate for the non-MF manuscript's Theorem C

`TheoremCLiteratureReductionCheck.lean` is a green development driver: it
checks that every reduction layer elaborates while the six final source leaves
are being formalized.  This file is the deliberately stricter completion
target.  It must not pass until each leaf and the assembled endpoints depend
only on Lean's accepted logical axioms (`propext`, `Classical.choice`, and
`Quot.sound`).

Run it with

```
lake env lean scripts/TheoremCCompletionAudit.lean
```

The source-side companion is
`python3 scripts/check_non_mf_unconditional.py --strict`, which also rejects
any direct `sorry`, `admit`, or `axiom` declaration anywhere in the non-MF
manuscript tree.
-/

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullHypEmbeddedConeOff
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullYiSuitableFiniteFamily
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullLemma44Canonical
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullLemma49KernelPower
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.hullSection6Relator
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.kotowskiOllivier
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.smallCancellationQuotient
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.osinTheorem12

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.minasyanOsin
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.hullCommonQuotient
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.literatureInputs
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_closed
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_closed
