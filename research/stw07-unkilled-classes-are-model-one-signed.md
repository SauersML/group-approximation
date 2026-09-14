---
rg: 2
id: stw07-unkilled-classes-are-model-one-signed
kind: claim
title: A K_0-class not killed by a faithful model has one sign across all models
distinct_from:
  stw07-sign-changing-qd-trace-values-kill-class: that detects both signs through quasidiagonal traces; this is the sign dichotomy at the level of models, which traces see only at the scale of the model dimension.
  stw07-trace-invisible-classes-carry-hahn-banach: that shows traces can be made blind to every class; this isolates the model-level invariant that must decide such classes.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**ESTABLISHED.**  Let `A` be separable, unital and quasidiagonal, and
`x in K_0(A)`.  A *model* is a sequence of c.c.p. maps `A -> M_(k_n)` that is
asymptotically multiplicative; its value on `x` is the eventual integer rank
difference.  Exactly one of the following holds:

1. some faithful model has value `0` on `x` (the K_0-Hahn--Banach conclusion);
2. every model is eventually `>= 0` on `x`, and every faithful model is
   eventually `> 0`;
3. every model is eventually `<= 0` on `x`, and every faithful model is
   eventually `< 0`.

*Proof.*  Subsequences and reindexings of models are models.  If some model
has infinitely many negative values and another infinitely many positive
values, pass to subsequences with eventually constant signs.  Then balance
any faithful model against them with `n`-dependent multiplicities, as in
`stw07-sign-changing-qd-trace-values-kill-class`, giving (1).  Otherwise one
sign never occurs infinitely often.  Say negative values do not, so every
model is eventually `>= 0`; if (1) fails, no faithful model has value `0`
infinitely often, so faithful models are eventually `> 0`.  The three cases
are mutually exclusive by definition.

So a trace-invisible class that is not killed is one-signed on every model,
at scale `o(k_n)`: a strict positivity invariant finer than every trace.
