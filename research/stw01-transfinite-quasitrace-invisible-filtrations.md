---
rg: 2
id: stw01-transfinite-quasitrace-invisible-filtrations
kind: claim
title: Arbitrary transfinite filtrations by quasitrace-invisible layers remain invisible
distinct_from:
  stw01-qt-invisible-ideal-extension-principle: that is a one-extension transfer theorem; this theorem iterates ideal invisibility through an arbitrary ordinal, including limits of uncountable cofinality.
  stw01-directed-limits-preserve-qt-linearity: that concerns C*-inductive limits whose stages already have quasitrace linearity; this theorem concerns continuous ideal filtrations whose successor quotients have no bounded quasitraces at all.
  stw01-stable-ideal-extensions-force-qt-linearity: that handles one stable ideal; this theorem permits arbitrarily many successor layers and only assumes bounded-quasitrace invisibility of each layer.
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `J` be a C\*-algebra.  Suppose an ordinal `gamma` and an increasing
family of closed two-sided ideals `(J_alpha)_(alpha<=gamma)` satisfy

```text
J_0=0,       J_gamma=J,
J_lambda=closure(union_(alpha<lambda) J_alpha)          (lambda limit),
```

and every successor quotient `J_(alpha+1)/J_alpha` carries no nonzero
bounded `2`-quasitrace.  Then `J` carries no nonzero bounded
`2`-quasitrace.

Consequently, if `J` is an ideal of a C\*-algebra `A` and every bounded
`2`-quasitrace on `A/J` is a trace, then every bounded `2`-quasitrace on `A`
is a trace.

In particular, the conclusion holds whenever every successor quotient in
the filtration of `J` is stable and the terminal quotient `A/J` is exact.
There is no restriction on the ordinal, its cofinality, or separability of
the algebras.
