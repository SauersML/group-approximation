import GroupApproximation.Manuscript.NonMF.TheoremCAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Kernel completion gate for the non-MF manuscript's Theorem C

## Superseded (2026-09-13)

Ten of the thirteen declarations audited below no longer exist, so this file
does not elaborate, and nothing in the repository runs it.

* `TorsionFree.hullLemma44Canonical`, `TorsionFree.hullLemma49KernelPower`,
  `TheoremC.kotowskiOllivier`, `TheoremC.smallCancellationQuotient`,
  `TheoremC.hullCommonQuotient`, `TheoremC.literatureInputs`,
  `TheoremC.manuscriptTorsionFreeFullMFRadical_openAdmissions` and
  `TheoremC.manuscriptTorsionFreeSimplified_openAdmissions` were retired with the
  `sorry`s of `Manuscript/NonMF/TheoremCAssembly.lean`; that module's header,
  "What was retired on 2026-09-13", says what replaced them.
* `TorsionFree.hullHypEmbeddedConeOff` and `TorsionFree.hullSection6Relator` had
  left that module earlier.

The completion target has no single declaration to audit yet.  Theorem C is now
`TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` and
`TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaInputs`, over the three
hypotheses `hgreendlinger`, `hbridge` and `hKO`.  `TheoremCAssembly` audits them
with `#audit_axioms`, and its closed leaves (`TheoremC.chiodo`,
`TheoremC.osinTheorem12`, `TheoremC.minasyanOsin`,
`TheoremC.hullFreeProductUnionGeometry`) with `#audit_closed_axioms`.
`Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean` states Theorem C with `hKO`
replaced by the three systolic leaves of `Kazhdan/KotowskiOllivierClosed.lean`.
The audits below are kept as the record of the earlier target.

## The earlier target

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
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeFullMFRadical_openAdmissions
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.manuscriptTorsionFreeSimplified_openAdmissions
