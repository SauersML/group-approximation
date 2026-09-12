---
rg: 2
id: mf-to-weak-qd-citation-has-unproved-lifting-step-proof
kind: route
title: Compare approximation hypotheses and exhibit a separating nonpositive MF witness
target: mf-to-weak-qd-citation-has-unproved-lifting-step
requires: []
artifacts:
  - research/artifacts/operator-mf-weak-quasidiagonality-audit-2026-09-11.md
---

The artifact, Sections 1--3, checks Dadarlat's Definitions 3.1 and 3.10 and
Proposition 3.19 in the primary text. It proves the definitional implication
from weak quasidiagonality to MF by polar decomposition. For the reverse
operation, the matrices `diag(-1,exp(i/n))` assigned to the involution of
`C_2` form a separating MF approximation but are not selfadjoint, so they
cannot be images of that involution under any positive linear map on the
full group C*-algebra. Thus the required completely positive approximation
does not arise just by extending the given maps. The cited route provides
no replacement maps or lifting theorem, and Proposition 3.19 retains its
stronger hypothesis. This proves the stated defect in that route, without
asserting a counterexample to the existential MF-to-weak-QD implication.
