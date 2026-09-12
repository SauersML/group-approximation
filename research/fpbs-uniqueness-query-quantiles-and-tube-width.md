---
rg: 2
id: fpbs-uniqueness-query-quantiles-and-tube-width
kind: claim
title: Near-critical uniqueness forces typical query expenditure and a walk-tube width constraint
artifacts:
  - research/artifacts/fpbs/query-strong-converse.md
---

For every fixed uniqueness parameter q>c and budget b<lambda/k(q,c),
successful connection by b*n queries, conditional on both endpoints
being infinite, has probability at most theta(q)^(-2) exp(-eta*n).
On a common probability space, path-production cost T_n (infinity
on failure) has liminf T_n/n>=lambda/k(q,c) almost surely.
Near c the sharp quadratic constant in this bound is 2c(1-c)lambda.
A radius-R walk tube with subexponential connection probability must
satisfy |B(o,R)|>=2lambda/(d*k(q,c)); such radii along q decreasing
to c must be at least 2 log(1/(q-c))/log(d-1)+O_G(1).
Existence of such tubes or a cheap certificate construction is not claimed.
