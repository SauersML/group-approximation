---
rg: 2
id: culf-mastel-rstar-commutativity-replacement-rows-peel-off
kind: claim
title: The final non-TVF R-star commutativity-replacement rows lie outside the two-tail kernel
distinct_from:
  culf-mastel-rstar-two-tail-core-is-not-specified: that concerns the internally unspecified NP pp gadgets; this identifies and completely removes the one explicit row gadget in the final reduction.
  culf-mastel-rstar-fixed-language-gap-is-published: that uses Proposition 6.2 to eliminate empty constraints with constant soundness; this audits the same replacement at the exact incidence level.
---

**ESTABLISHED CITATION CONSEQUENCE.**  In the specialization of
Culf--Mastel Proposition 6.2 to the four-ary relation `R_*`, each empty
two-variable constraint on `{x,y}` is replaced by one `R_*` occurrence on

```text
{x,y,z_(i,1),z_(i,2)},                                  (RCP1)
```

where the two variables `z_(i,1),z_(i,2)` are freshly introduced for that
occurrence.  They have active degree one, so every such replacement row is
immediately eligible for two-tail peeling.  In reverse reconstruction one
retains `x,y` and cap-completes the two fresh variables.

Consequently the commutativity gadgets used after subdivision add no row to
the terminal two-tail kernel.  The unresolved dense kernel comes from the
atomic `R_*` rows inside the pp gadgets selected through NP-completeness (and
their visible/internal overlaps), not from the final removal of empty
constraints.

Primary source: Culf--Mastel, arXiv:2410.21223v2, Proposition 6.2, especially
the fresh variables `z_(i,w)` in its proof, followed by Theorem 6.8.

