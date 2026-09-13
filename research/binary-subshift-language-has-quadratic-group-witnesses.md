---
rg: 2
id: binary-subshift-language-has-quadratic-group-witnesses
kind: claim
title: Binary block occurrence has quadratic-length witnesses in the three-generator elementary group
distinct_from:
  subshift-elementary-group-word-problem-degree: that proves Turing equivalence for minimal subshifts; this gives a uniform quadratic many-one reduction and a linear window bound for every nonempty binary subshift.
artifacts:
  - research/artifacts/pestov91-marked-subshift-encoding-2026-09-13.md
---

For any nonempty binary subshift `X`, mark
`G_X=EL_3(LC(X,F_2) semidirect Z)` by the explicit triple `(c,t,w)` of
orders `7,2,2` from the unit-idempotent theorem.

A uniform polynomial-time construction assigns each binary word `a` of
length `n>=1` a group word `W_a` of length at most `2^17 n^2`, with
`W_a=1 in G_X` exactly when `a` is absent from `X`. Thus language
membership reduces many-one to the complement of the word problem.

Relations of length at most `l` are determined by `L_(2l+1)(X)`. More
precisely, the word problem reduces uniformly by a nonadaptive truth
table to language queries of that single length. No polynomial bound
on the number of queries in this direction is asserted.
