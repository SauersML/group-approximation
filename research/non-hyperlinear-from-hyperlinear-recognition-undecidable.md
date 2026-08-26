---
rg: 2
id: non-hyperlinear-from-hyperlinear-recognition-undecidable
kind: route
title: An undecidability proof for hyperlinear recognition produces a non-hyperlinear group without constructing one
target: non-hyperlinear-group
requires:
  - hyperlinear-recognition-undecidable
---

## Why sufficient

If every group were hyperlinear, `HYP_fp` would be the set of all codes,
which is decidable.  So undecidability forces a finitely presented
non-hyperlinear group to exist; by
[[approximation-property-recognition-dichotomy]] the reduction that proves
undecidability then also proves `Pi^0_2`-completeness on two-generator
recursive presentations.

## What is and is not explicit

This route is non-constructive in the sense of MIP* = RE: it yields a
computable family `e |-> G_e` of finite presentations of which some member
is non-hyperlinear, together with an algorithm that, from any putative
decision procedure, produces a contradiction.  It does not name the member.
A proof along this route therefore resolves the goal at the level at which
Connes' embedding problem was resolved, and the goal node's refutation
doctrine already treats that level as a program resolution.  Anyone who
prefers a named group afterwards may search the family: by the
finite-table certificate of
[[local-approximation-properties-are-marked-closed]], non-hyperlinearity of a
member is a `Sigma^0_2` event that becomes checkable once its witnessing
table and tolerance are guessed.
