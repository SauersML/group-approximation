---
rg: 2
id: brick-host-nonisomorphism-via-isotropy-strata
kind: route
title: "Separate G_2^n from the W1 host by the cardinality of the top isotropy stratum, and from the RS host by the residual stabilizer question"
target: brick-groupoid-not-isomorphic-to-kazhdan-host
requires:
  - brick-groupoid-has-no-principal-cantor-factor
  - brick-groupoid-not-isomorphic-to-rs-boundary-host
---

The target asserts two non-isomorphisms, `G_2^n ≇ 𝒢_W1` and `G_2^n ≇ 𝒢_RS`, for every
`n ≥ 1`.

**W1 half (done).** `𝒢_W1 = (M ⋊ Γ) × G_2`, where `Γ ↷ M` is free on a Cantor set by Step 3 of
`amenable-purely-infinite-groupoid-kazhdan-host-proof`. So `M ⋊ Γ` is principal with
uncountable unit space. `brick-groupoid-has-no-principal-cantor-factor` (c).1 and (c).2 give
`G_2^n ≇ 𝒢_W1` for all `n`. The argument uses only the isotropy groups of arrows, so it also
rules out abstract (discontinuous) groupoid isomorphisms, and by (c).3 it rules out
isomorphisms between nonempty open reductions.

**RS half.** This is exactly `brick-groupoid-not-isomorphic-to-rs-boundary-host`. The
isotropy obstruction has already reduced it to non-free boundary actions whose maximal
stabilizer rank is `n − 1 ≥ 1` and is attained only on a countable set.

The route does not use `brin-thompson-groups-nv-are-a-t-menable`, unlike
`brick-host-nonisomorphism-from-nv-haagerup`. So it is an independent route to the target,
not a circular one.
