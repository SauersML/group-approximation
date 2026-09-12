---
rg: 2
id: nonhyperlinear-from-independent-set-hybrid-rank-router
kind: route
title: Turn the independent-set overlap gap into a rank-conjugacy word-energy floor
target: non-hyperlinear-group
requires:
  - fixed-nonru-independent-set-orthogonality-game-exists
  - outcome-count-free-subpovm-completion
  - independent-finite-clocks-round-to-arbitrary-row-pvms
  - rank-conjugacy-detects-projection-overlap
  - hybrid-rank-router-authenticates-affine-overlap-blocks
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
---

Use one independent finite clock per question on the marked corner.  Fixed
torsion and commutator rounding give genuine row PVMs with total movement
bounded by the presentation defect and with no outcome-count loss.  The
hybrid router supplies `(HRR1)--(HRR2)` for every forbidden pair.  Hence
`(RCD3)` gives

```text
E_rel>=c L_I^2-o(1)>=c delta_0^2-o(1)                 (NHR1)
```

after normalization by the marked-corner mass, for one dimension-independent
`c>0`.

The perfect commuting row-PVM strategy has every forbidden overlap zero.
By `(RCD2)`, each stable conjugator exists, so it extends to an exact tracial
representation of the finite presentation with nonzero marked corner.  The
mark is therefore a nontrivial abstract group element.

If that group were hyperlinear, canonical-trace matrix microstates would
have vanishing relator defect while keeping the nontrivial marked involution
at canonical distance, hence keeping its corner at fixed positive trace.
After division by this mass, `(NHR1)` contradicts vanishing defect.  The
group is not hyperlinear.

