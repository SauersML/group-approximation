---
rg: 2
id: linear-sofic-nonsofic-group
kind: claim
title: Exhibit a linear sofic group that is not sofic
root: true
distinct_from:
  hyperlinear-nonsofic-group: that separates hyperlinearity from soficity (Pestov 3.4); this separates complex linear soficity from soficity, and no implication between hyperlinear and linear sofic is known in either direction.
  weakly-sofic-not-sofic: that is the settled separation for weak soficity; this is the open separation one step lower in the chain.
---

OPEN.  Exhibit a countable group that is linear sofic over `C` but not sofic.

Arzhantseva--Paunescu, arXiv:1212.6780, after Proposition 4.5: "The following
result shows that linear soficity is a priori weaker than soficity. Observe
that the converse is open."  Question 8.5 asks: "Are all linear sofic groups
indeed sofic?"

Before August 2026 the question was out of reach, because no nonsofic group
was known.  Now the candidates are the known nonsofic groups:

- the Leavitt unit group of [[openai-leavitt-unit-nonsofic]];
- the Kun--Thom wreath of [[kun-thom-nonsofic-wreath]].

## Attempts

- **Kun--Thom wreath.** [[sofic-linear-weakly-sofic-chain-has-a-strict-link]]
  says that deciding whether `W` is `C`-linear sofic settles which inclusion is
  strict.  The positive side is [[kun-thom-wreath-linear-sofic]].  Glebsky's
  permanence (residually finite quotient over a weakly sofic kernel) has no
  known rank-metric analogue, and his equation characterization does not
  retain the rank metric.
- **Leavitt unit group.** Not attempted here.  A characteristic-two Kaplansky
  failure would push it the other way; see [[non-linear-sofic-group]].
- **The complex-linear row of the defect criterion (2026-09-12, lane
  `weakly-sofic-extension`).**
  - A `C`-linear sofic group carrying a nontrivial rigid defect is nonsofic,
    which answers Question 8.5 ([[linear-sofic-nonsofic-via-c-rank-row-defect]],
    needing [[c-linear-sofic-group-carries-nontrivial-rigid-defect]]).
  - The opposite outcome, [[c-linear-sofic-groups-kill-rigid-compression-defects]],
    settles [[non-linear-sofic-group]] over `C` instead.
  - Algebraic models of localization pairs normalize, so a witness needs
    non-algebraic rank models.
  - Property (T) forces no rank rounding over `C`
    ([[kazhdan-rank-rounding-fails-over-every-field]]), so such models are not ruled
    out.
