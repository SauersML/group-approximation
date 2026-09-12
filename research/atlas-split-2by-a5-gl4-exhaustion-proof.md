---
rg: 2
id: atlas-split-2by-a5-gl4-exhaustion-proof
kind: route
title: Exhaust split perfect two-by-A5 images in GL4(3)
target: atlas-no-split-perfect-2-extension-of-a5-acts-on-f3-four-space
requires: []
artifacts:
  - experiments/atlas_a4_q1920_split_2byA5_gl4_classification.g
  - experiments/verify_atlas_q1920_finite_certificates.py
  - research/artifacts/atlas-a4-q1920-split-2byA5-gl4.json
---

Exact arithmetic gives

```text
|GL4(3)|=(81-1)(81-3)(81-9)(81-27)=24261120,
v_2(|GL4(3)|)=9.
```

A split perfect extension `R semidirect A5` embedded in `GL4(3)` therefore
has `|R|=2^a`, `0<=a<=7`.  GAP's complete perfect-group library at the eight
orders `60*2^a` is filtered by three exact predicates: its Fitting subgroup
has order `2^a`, the quotient is simple of order sixty, and an `A5`
complement exists.  Exactly nine groups survive (at exponents
`0,4,5,6,7`).

For every survivor the verifier enumerates all irreducible
four-dimensional `F3` modules and computes their image orders.  Each group
has one such module.  The trivial-radical case has image order sixty; every
one of the eight nontrivial-radical cases also has image order sixty, so none
is faithful.  The adjacent nonsplit group `PerfectGroup(1920,6)` is checked
as an edge case: it has a faithful image of order 1920 but zero complement
classes, and is therefore outside the split statement.  The independent
audit recomputes the ambient order and 2-adic bound and checks all nine
archived profiles.
