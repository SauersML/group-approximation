---
rg: 2
id: stw01-transfinite-null-ideal-induction-proof
kind: route
title: Carry the square-null ideal through successors and arbitrary limits
target: stw01-transfinite-quasitrace-invisible-filtrations
requires:
  - stw01-stable-algebras-are-bounded-quasitrace-invisible
  - stw01-qt-invisible-ideal-extension-principle
---

Fix a bounded `2`-quasitrace `q` on `J`, and let

```text
N_q={x in J:q(x*x)=0}.
```

The standard null-ideal lemma says that `N_q` is a closed two-sided ideal and
that `q` factors through a bounded `2`-quasitrace on `J/N_q`.  We prove by
transfinite induction that

```text
J_alpha subset N_q       (alpha<=gamma).               (1)
```

The assertion is immediate at `0`.  Suppose it holds at `alpha`.  Because
`J_alpha subset N_q`, the quasitrace factors through `J/J_alpha`; restrict
the induced quasitrace to the ideal `J_(alpha+1)/J_alpha`.  The successor
hypothesis makes this restriction zero.  Equivalently, every element of
`J_(alpha+1)` lies in `N_q`, proving (1) at `alpha+1`.

Now let `lambda<=gamma` be a limit ordinal and suppose (1) holds below
`lambda`.  The ideal `N_q` is closed and contains every `J_alpha` for
`alpha<lambda`; hence it contains

```text
closure(union_(alpha<lambda) J_alpha)=J_lambda.
```

This argument does not choose a cofinal sequence, so it applies unchanged at
limits of arbitrary cofinality.  Induction gives `J=J_gamma subset N_q`, and
therefore `q=0`.  Since `q` was arbitrary, `J` is bounded-quasitrace-invisible.

If `J ideal A` and bounded quasitraces on `A/J` are traces, apply
`stw01-qt-invisible-ideal-extension-principle` to obtain quasitrace linearity
on `A`.

For the final corollary, every stable successor layer is
bounded-quasitrace-invisible by
`stw01-stable-algebras-are-bounded-quasitrace-invisible`, while Haagerup's
theorem makes every bounded `2`-quasitrace on the exact quotient `A/J` a
trace.  The preceding two conclusions apply.

**Trust boundary.**  The only general quasitrace input is the standard fact
that the square-null space of a bounded `2`-quasitrace is a closed two-sided
ideal through which the quasitrace factors.  The successor and limit steps
are explicit and require neither separability nor countable cofinality.
