---
rg: 2
id: stw01-transfinite-qt-linearity-filtrations
kind: claim
title: Quasitrace linearity is closed under arbitrary continuous ideal filtrations
distinct_from:
  stw01-extensions-preserve-qt-linearity: that proves one arbitrary unital extension; this iterates the same net splitting through successor stages and handles limit ordinals without any cofinality or separability assumption.
  stw01-transfinite-quasitrace-invisible-filtrations: that assumes every successor layer carries no nonzero bounded quasitrace; here the layers may carry arbitrary traces and only their quasitraces are required to be linear.
  stw01-directed-limits-preserve-qt-linearity: that treats unital C*-inductive systems by local approximation; intermediate members of an ideal filtration need not be unital, so the present proof instead inducts on restrictions of one ambient quasitrace.
artifacts:
  - research/artifacts/stw01-transfinite-linearity-audit-2026-08-30.md
---

Let `A` be a unital C*-algebra.  Suppose an ordinal `gamma` and an
increasing family of closed two-sided ideals `(I_alpha)_(alpha<=gamma)`
satisfy

```text
I_0=0,       I_gamma=A,
I_lambda=closure(union_(alpha<lambda) I_alpha)          (lambda limit),
```

and every bounded `2`-quasitrace on every successor quotient

```text
I_(alpha+1)/I_alpha
```

is a trace.  Then every bounded `2`-quasitrace on `A` is a trace.

Consequently, if a unital algebra with such a continuous filtration is a
counterexample to Problem I, at least one successor quotient is already a
counterexample.  The filtration can have arbitrary ordinal length and
cofinality; the ideals and quotients need not be separable, exact,
sigma-unital, stable, quasitraceless, or unital.
