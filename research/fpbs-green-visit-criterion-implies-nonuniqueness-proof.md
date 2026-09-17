---
rg: 2
id: fpbs-green-visit-criterion-implies-nonuniqueness-proof
kind: route
title: Uniqueness makes the two-point function bounded below by theta squared
target: fpbs-green-visit-criterion-implies-nonuniqueness
requires: []
artifacts:
  - research/artifacts/fpbs/docs/green-visit-kernel-2026-09-17.md
---

Complete proof in Section 3 of the artifact.

1. Each `a_n` is nondecreasing in `p`, so `A` is too.
2. Suppose `p'<=p` has a unique infinite cluster. Then `theta(p')>0`.
   Harris–FKG gives `P(e<->infinity, x<->infinity) >= theta(p')^2`.
   Uniqueness turns this event into `e<->x`, so `tau_(p')>=theta(p')^2`
   everywhere.
3. Therefore `a_n(p')>=theta(p')^2` for all `n`, and
   `A(p)>=A(p')=infinity`.
4. If `p>p_c`, no parameter in `[0,p]` has a unique infinite cluster, so
   `p_u>=p>p_c`.
