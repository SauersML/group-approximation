---
rg: 2
id: sl3z-ozawa-block-qt-via-kernel-property-s
kind: route
title: Property (S) of the corona trace kernel excludes bounded quasitraces on it, so every quasitrace of the corona vanishes there
target: sl3z-ozawa-block-algebra-quasitraces-are-traces
requires: [sl3z-ozawa-corona-trace-kernel-has-property-s, sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible]
artifacts:
  - research/artifacts/quasitrace-kernel-maximal-ideal-property-s-2026-09-12.md
---

Proof: artifact §2, Prop 2.1.

1. **No quasitraces on `K`.** A separable C*-algebra with property (S) has no nonzero
   bounded 2-quasitrace. This is the "only if" half of Ortega–Perera–Rørdam,
   arXiv:0903.2917v4, Prop 4.5, whose proof handles an arbitrary bounded
   2-quasitrace through its lower-semicontinuous dimension function. The statement
   was checked against the PDF.
2. **Restriction.** A bounded 2-quasitrace on `A` restricts, through
   `M_2(K) ⊂ M_2(A)`, to a bounded 2-quasitrace on `K`. By step 1 the restriction is
   zero.
3. **Conclusion.** This is condition 2 of
   `sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible`. So every bounded
   2-quasitrace on `B` is a trace.

Every stable C*-algebra has (S) (OPR §4). So this route logically contains
`sl3z-ozawa-block-qt-via-stable-kernel`, which is kept as the named special case.
