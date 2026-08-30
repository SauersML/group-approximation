---
rg: 2
id: fu-locally-finite-nucdim-completions-have-only-uniform-traces
kind: claim
title: Stable-rank-one locally finite nuclear-dimension completions have only uniform traces
distinct_from:
  stw99-problem-xxii-tracial-completion-traces: that asks for every compact-trace-space C-star algebra; this theorem assumes algebraic simplicity, separability, non-elementarity, stable rank one, and locally finite nuclear dimension.
  stw22-zero-dimensional-factor-bundles-have-uniform-traces: that internal theorem assumes a zero-dimensional bundle base and no presentation by a dense stable-rank-one algebra; this literature theorem has no dimension hypothesis on the trace simplex but imposes regularity on the dense algebra.
artifacts:
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

Let `A` be an algebraically simple, separable, non-elementary, stable-rank-one
C-star algebra such that `T(A)` is nonempty and compact.  If `A` has locally
finite nuclear dimension, then its uniform tracial completion satisfies

```text
T(completion_(2,T(A))(A)) = T(A).
```

More precisely, the tracial completion is a hyperfinite type `II_1`
factorial tracially complete C-star algebra isomorphic, as a tracially
complete pair, to the hyperfinite model `(R_(T(A)),T(A))`.  It is amenable,
McDuff, has property Gamma and complemented partitions of unity, while its
underlying C-star algebra is pure and has real rank zero and stable rank one.

Thus every trace on this completion is one of the designated uniformly
`2`-norm-continuous traces, giving an exact positive class for STW Problem
XXII.
