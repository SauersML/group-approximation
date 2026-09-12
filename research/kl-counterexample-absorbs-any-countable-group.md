---
rg: 2
id: kl-counterexample-absorbs-any-countable-group
kind: claim
title: A Kervaire--Laudenbach counterexample can be forced to contain any prescribed countable group
invalidates: [kl-counterexample-screening-by-local-subgroup-structure]
distinct_from:
  kl-counterexample-can-be-finitely-presented: that shrinks a counterexample to finite presentation data, and is a statement about where to search; this enlarges one to contain a prescribed group, and is a statement about what cannot be excluded by searching.
  kl-counterexample-can-be-two-generator-simple: that is the reduction to simple coefficient groups; this amplifies it by noting that the simple envelope can be made to swallow any countable group first, so the reduction confers no structural information about counterexamples.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

If `kervaire-laudenbach-nonsingular-conjecture` fails at all, then for every
countable group `A` it fails over a two-generator nonabelian simple group
containing an isomorphic copy of `A`.

## What it excludes

Any attempt to characterize, recognize or screen counterexamples by inherited
local structure.  Torsion spectrum, excluded or required subgroups, amenable
subgroups, local finiteness, elementary-amenability, orderability — every
property of the form "contains / does not contain a copy of `A`" is blind
here, because both answers are compatible with being a counterexample the
moment any counterexample exists at all.

This is a real constraint on this repository's own habits.  The natural
instinct, when asked whether a specific group violates the conjecture, is to
look at what sits inside it; that instinct is provably uninformative, and the
route built on it is recorded dead as
`kl-counterexample-screening-by-local-subgroup-structure`.

## What it does not exclude

Properties that are **not** inherited from countable subgroups: hyperlinearity
is the example that matters here, since
`kervaire-laudenbach-holds-for-hyperlinear` really does exclude counterexamples
and is not of the "contains a copy of" form.  The obstruction is against local
subgroup data, not against approximation properties of the whole group.
