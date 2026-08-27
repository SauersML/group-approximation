---
rg: 2
id: literal-canonical-trace-hyperlinear-not-quasidiagonal-proof
kind: route
title: Composition of the sofic hyperlinear bridge with the not-MF-trace endpoint
target: literal-canonical-trace-hyperlinear-not-quasidiagonal
requires: []
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean
  - GroupApproximation/Analysis/SoficHyperlinearBridge.lean
  - GroupApproximation/Sofic/LiteralTraceConsequence.lean
---

Direct proof, two compositions of theorems already in the tree.

Hyperlinear clause: `canonicalMaximalTrace_isHyperlinearTrace_of_isSofic
MarkedGroup markedGroup_isSofic`.

Non-quasidiagonal clause: given `M : QuasidiagonalTraceModel τ_E`,
`M.toMFTraceModel ucpContractive : ShulmanTrace.MFTraceModel τ_E`, contradicting
`markedGroup_canonicalMaximalTrace_not_isMFTrace`.

A Lean module stating the conjunction verbatim is being authored
(`GroupApproximation/Manuscript/NinetyNineProblems/`); until it lands the two
cited modules carry the two halves.

Landed: `NinetyNineProblems.literalCanonicalTrace_isHyperlinearTrace`,
`literalCanonicalTrace_not_isQuasidiagonalTrace` and their conjunction in
`GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean` (2dbea8f73).
