---
rg: 2
id: infinite-simple-kazhdan-hyperlinear-group
kind: claim
title: Some infinite simple group with Kazhdan's property (T) is hyperlinear (Pestov Open Question 9.1, after Ozawa)
root: true
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that is the yes/no question for one explicit group; this is the existential question from the literature, which that group would answer positively but whose negation it cannot supply.
  kac-moody-lattice-is-non-hyperlinear-or-llp-failure: that is a proved dichotomy for the Caprace--Remy lattices; this is the open existence question the dichotomy constrains without deciding.
  simple-kazhdan-kac-moody-lattices-exist: that asserts existence of infinite finitely presented simple Kazhdan groups; this asks for one that is in addition hyperlinear.
  kazhdan-mf-hyperlinear-fragment: that proves simple Kazhdan groups that are weakly MF are hyperlinear; the hypothesis is never met, since every infinite simple Kazhdan group has full MF radical, so that fragment does not touch this question.
---

**OPEN.** There exists an infinite simple group with Kazhdan's property (T)
that is hyperlinear.

## Source

V. G. Pestov, *Hyperlinear and sofic groups: a brief guide*, Bull. Symbolic
Logic 14 (2008), arXiv:0804.3968, Section 9, page 21 of the arXiv PDF, read
from the PDF on 2026-09-11:

> **Open question 9.1** (Cf. Ozawa [64]). Let G be an infinite simple group
> with Kazhdan's property (T). Can it be hyperlinear (sofic)?

Pestov lists it with Question 9.4 as one of "the two candidates for a
counter-example". This node records the hyperlinear half. The sofic half is
strictly stronger, because sofic groups are hyperlinear.

## Why it is a root of this graph

Every Leavitt candidate in this development is infinite, simple and Kazhdan.
The binary Leavitt unit group `L_(F_2)(1,2)^x` is simple and has property
(T), so a positive answer to `binary-leavitt-unit-group-hyperlinear`, and
hence the unstable branch `leavitt-steinberg-hs-unstable`, answers this
question positively. That group is nonsofic (`openai-leavitt-unit-nonsofic`),
so it can only witness the hyperlinear half. The route
`simple-kazhdan-hyperlinear-from-leavitt-unit-group` records the implication.

It calibrates the unstable Steinberg branch: that branch implies a positive
answer to a named open question, in addition to the Question 3.4 separation
and hyperlinearity of Thompson's `V`.

## Attempts

- **Leavitt unit group.** The route above. It needs
  `binary-leavitt-unit-group-hyperlinear`, which is open; the finite forms of
  that obligation are `binary-leavitt-hyperlinear-iff-24k-feasible` and the
  regular-atlas criterion.
- **Caprace--Remy Kac--Moody lattices.** `kac-moody-lattice-is-non-hyperlinear-or-llp-failure`
  proves only a dichotomy with failure of the local lifting property; no
  hyperlinearity is produced.
- **Operator-norm microstates.** Dead for every candidate:
  `simple-kazhdan-groups-have-full-mf-radical` makes every infinite simple
  Kazhdan group non-MF, so the weakly MF fragment `kazhdan-mf-hyperlinear-fragment`
  never applies.
- **Stability shortcuts.** Dead by hypothesis. Becker--Lubotzky
  (arXiv:1809.00632, Theorem 1.3) and Fournier-Facio--Gerasimova--Spaas
  (arXiv:2307.13155, Theorem 6.1) show that an infinite hyperlinear Kazhdan
  group is neither HS-stable nor locally HS-stable. A positive witness must
  therefore carry almost-representations that are far from genuine ones,
  and an infinite simple Kazhdan group has no nontrivial genuine
  finite-dimensional unitary representation to seed them.
