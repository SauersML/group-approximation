---
rg: 2
id: labbe-wang-shift-crossed-product-is-not-exactly-matricial
kind: claim
title: The Labbé Wang shift crossed product has no unital embedding in any algebraic ultraproduct of matrix algebras over fields
distinct_from:
  labbe-wang-shift-crossed-product-is-exactly-matricial: that is the positive polarity; this is its negation
  leavitt-algebra-has-no-unital-rank-model: that forbids even rank-metric models, for a paradoxical algebra; this forbids only exact algebraic models, for a stably finite algebra that does have a rank model
---

**OPEN.** Let `R = LC(Ω_U, F_q) ⋊ Z^2`, for Labbé's Wang shift `Ω_U`. Then `R` does not embed unitally in any algebraic
ultraproduct of matrix algebras over fields.

**Payoff.** `R` would be the first simple, finitely generated, stably finite ring on main that is not exactly matricial.
It carries a unital rank model, and its elementary groups are simple mod centre, Kazhdan and linear sofic. So those
groups separate `stably-finite-simple-rings-have-mf-elementary-groups` from
`stably-mf-elementary-groups-force-matricial-rings`: whichever way their MF status goes, one of the two U3 converses
fails.

Route: `labbe-crossed-product-not-matricial-from-finite-presentation`, from gate (a) of the ring route.
