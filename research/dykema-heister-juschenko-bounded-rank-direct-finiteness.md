---
rg: 2
id: dykema-heister-juschenko-bounded-rank-direct-finiteness
kind: claim
title: Direct finiteness over F_2 is settled for rank pairs (3,n) with n at most 11, and for (5,5)
distinct_from:
  direct-finiteness-not-inherited-by-quotients: that is a general permanence failure with a free-algebra witness; this is an imported positive result about small supports in group algebras, and the two are used together only in the support floor.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

Imported from Dykema--Heister--Juschenko, *Finitely presented groups related
to Kaplansky's direct finiteness conjecture*, Experimental Mathematics 24
(2015) 326--338, arXiv:1112.1790.

Say Kaplansky's Direct Finiteness Conjecture **holds over `K` for the rank
pair `(m,n)`** if for every group `G` and all `a, b` in `K[G]` with
`|supp a| = m` and `|supp b| = n`, `ab = 1` implies `ba = 1` (their
Definition 2.12; `m, n >= 2`).  Their exhaustive machine enumeration of the
ULIE groups over `K = F_2` gives:

> DFC and the Invertibles Conjecture hold over `F_2` for the rank pairs
> `(3,n)` with `n <= 11`, and for `(5,5)`.

By their Remark 2.13 the property for `(m,n)` is equivalent to that for
`(n,m)`, so the statement is symmetric in the two supports.

**Status: established, imported.**  The reduction to ULIE groups (their
Theorem 2.14) is an ordinary proof; the rank statement additionally rests on a
computer enumeration reported in their Section 6, which was not replayed here.
The trust surface is therefore one refereed computer-assisted computation, and
any node depending on it inherits that.  It is used once, in
`leavitt-rank-three-lift-inverse-support-thirteen`, and only in the negative
direction — to rule out small completions, never to certify one.

*(2026-08-18.)*  That single consumer no longer needs it: the route
`support-thirteen-from-no-inverse` derives the same conclusion from
`leavitt-rank-three-lift-has-no-one-sided-inverse`, which uses only coset
bookkeeping and Nagao's theorem.  So nothing established now depends on the
enumeration, and this node stands as a recorded literature fact rather than as
load-bearing input.  It keeps one live use, the parity remark of Remark 2.8
corroborating the augmentation argument.

Two of their side remarks are worth having on hand.  Remark 2.8: over `F_2` a
minimally realizable partition consists of pairs plus the singleton
`{(0,0)}`, so both ranks are odd — an internal corroboration of the parity
argument used downstream.  And their introduction records the surrounding
landscape: characteristic zero is Kaplansky's own, residually amenable is
Ara--O'Meara--Perera, sofic is Elek--Szabo (in the stronger stably finite
form, over division rings).  Positive characteristic is what remains, which is
why `openai-leavitt-unit-nonsofic` puts this lane next to that one.
