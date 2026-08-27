---
rg: 2
id: literal-canonical-trace-hyperlinear-not-quasidiagonal
kind: claim
title: The canonical trace of C*(E) is a hyperlinear trace that is not quasidiagonal
distinct_from:
  literal-central-mark-corona-invisible: that is the statement about group representations into the norm corona; this is its trace-level form on the whole of C*(E), paired with the positive Hilbert--Schmidt statement that soficity gives.
  literal-group-sofic: that is the permutation approximation; this is the pair of trace statements it feeds, one positive and one negative.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - GroupApproximation/Analysis/SoficHyperlinearBridge.lean
  - GroupApproximation/Sofic/LiteralTraceConsequence.lean
  - GroupApproximation/Analysis/QuasidiagonalTrace.lean
---

Let `E` be the literal finitely presented group and `τ_E` the canonical trace
of the full group C\*-algebra `C*(E)` (`canonicalMaximalTrace MarkedGroup`
on `MaximalGroupCStar MarkedGroup`).  Then

1. `τ_E` is a hyperlinear trace: `ShulmanTrace.IsHyperlinearTrace τ_E`
   (bounded linear `*`-preserving matrix models, asymptotically multiplicative
   in normalized Hilbert--Schmidt norm, recovering `τ_E`);
2. `τ_E` is not a quasidiagonal trace: `¬ Quasidiagonal.IsQuasidiagonalTrace τ_E`
   (no unital completely positive matrix models asymptotically multiplicative
   in operator norm recover `τ_E`).

**Established.**  Clause 1 is
`ShulmanTrace.canonicalMaximalTrace_isHyperlinearTrace_of_isSofic` applied to
`LiteralSoficAssembly.markedGroup_isSofic`.  Clause 2: a quasidiagonal model
is an MF-trace model (`QuasidiagonalTraceModel.toMFTraceModel`, with the
contractivity of u.c.p. maps discharged by `UCPContractiveMatrix.ucpContractive`),
and `LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace`
says there is none.  Underneath that: an MF-trace model of `τ_E` would make
`E` operator-MF (`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`),
and the central involution `mark ≠ 1` is sent to `1` by every corona
representation (`LiteralNonMFEndpoint.literal_mark_eq_one_in_unitaryCorona`),
so `E` is not operator-MF.

The distance between clause 1 and Brown's amenability of `τ_E` is complete
positivity of the models, i.e. `literal-group-factorization-property`.
