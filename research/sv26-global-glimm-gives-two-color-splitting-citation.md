---
rg: 2
id: sv26-global-glimm-gives-two-color-splitting-citation
kind: route
title: Import Seth--Vilalta Theorem 5.6, (i) implies (ii)
target: sv26-global-glimm-gives-two-color-splitting
requires: []
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

**Established by citation.**  Source: Seth--Vilalta, *Continuous functions over
a pure C*-algebra*, arXiv:2602.14809v2 (preprint), Theorem 5.6
(`prp:Gen_DimRed`), implication (i) implies (ii), with `L = 2(m+1)(M_1+2)`;
statement checked against the arXiv source on 2026-09-16.

Caveat for referees: SV present this implication as a list of modifications of
the proof of Antoine--Perera--Thiel--Vilalta, arXiv:2406.11052v3, Lemma 6.2:
reduce to the separable case with Thiel--Vilalta's separable inheritability
(DimCu2, Prop. 6.1), apply SV Lemma 5.4 with `N = M_1 + 2` where APTV use their
own divisibility, obtain `d_tau(e') <= (1-eps)(M_1+2) d_tau(y_1)` for every
lower semicontinuous 2-quasitrace, and conclude with `m`-comparison through
Robert, arXiv:1002.2180 (Munster J. Math. 4 (2011)), Lemma 1.  This is the
least detailed import in the artifact and was not re-derived line by line.  It
is used only by `pure-tensor-nucdim-factor-pure-iff-global-glimm`, not by
`pure-tensor-nucdim-no-pi-quotient-is-pure`.
