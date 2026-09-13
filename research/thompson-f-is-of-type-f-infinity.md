---
rg: 2
id: thompson-f-is-of-type-f-infinity
kind: claim
title: Thompson's group F is finitely presented and has a K(F,1) with finitely many cells in each dimension, so it is of type F_infinity
distinct_from:
  thompson-f-has-infinite-cohomological-dimension: that records cd F = infinity (F is torsion-free and contains Z^n for every n); this records the finiteness property F_infinity, which Brown–Geoghegan prove for the same infinite-dimensional group.
---

**ESTABLISHED (literature import).** Richard Thompson's group `F`, given by the
presentation `< x_0, x_1, x_2, … | x_i^(−1) x_n x_i = x_(n+1) for i < n >`, is
finitely presented, and it has an Eilenberg–MacLane space `K(F,1)` with finitely
many cells in each dimension. So `F` is of type `F_∞`, and in particular of type
`FP_∞`.

Import route: `thompson-f-is-of-type-f-infinity-citation`
(Brown–Geoghegan, Invent. Math. 77 (1984), pp. 367–368, read from the journal PDF).

**Why it matters here.** `F` is not elementary amenable
(`thompson-f-has-no-free-subgroups` records this with Cannon–Floyd–Parry §4). So
an amenability proof for `F` (`thompson-f-is-amenable`) would answer Zaremsky
Problem 1.12, and a proof that every amenable group of type `F_∞` is elementary
amenable (`every-f-infinity-amenable-group-is-elementary-amenable`) would prove
`thompson-f-is-not-amenable`.
