---
rg: 2
id: fu-tracial-completion-trace-equality-citation
kind: route
title: Import Fu's tracial-completion classification and trace equality
target: fu-locally-finite-nucdim-completions-have-only-uniform-traces
requires: []
artifacts:
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

Apply Xuanlong Fu, *Divisibility and Real Rank Zero*, arXiv:2605.21655v1
(2026-05-20), Theorem 10.12.  Its hypotheses are word-for-word those in the
target: `A` is algebraically simple, separable, non-elementary, has stable
rank one, has nonempty compact `T(A)`, and has locally finite nuclear
dimension.

The theorem states that the tracial completion
`(completion_(2,T(A))(A),T(A))` is hyperfinite type `II_1`, factorial, and
isomorphic to the hyperfinite model.  It also lists amenability, McDuffness,
property Gamma, complemented partitions of unity, pureness, real rank zero,
stable rank one, and, crucially,

```text
T(completion_(2,T(A))(A)) = T(A).
```

The final equality is precisely the trace-continuity conclusion used here;
the route neither drops a source hypothesis nor extends the theorem to an
arbitrary tracial completion.
