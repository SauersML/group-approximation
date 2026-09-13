---
rg: 2
id: every-braid-group-acts-properly-on-a-proper-cat0-space
kind: claim
title: Every braid group acts properly by isometries on a proper CAT(0) space
distinct_from:
  every-braid-group-is-cat0: that claim asks for a geometric (proper and cocompact) action; this one drops cocompactness and keeps the space proper
---

For every `n >= 1` there is a proper (complete and locally compact) CAT(0)
metric space on which `B_n` acts properly by isometries. "Properly" is meant as
in Bridson–Haefliger: every point has a ball whose translates meet it for only
finitely many group elements.

This is the reading of Zaremsky's second sentence in Problem 3.6 ("Even
without requiring cocompactness this is unknown") that stays in the setting of
CAT(0) groups. Two nearby readings change the question:

- if the space need only be complete, Hilbert spaces count, and a proper
  affine isometric action on a Hilbert space, i.e. the Haagerup property
  (`every-braid-group-has-the-haagerup-property`, Problem 3.7), would be
  enough;
- if the space need not be complete, Weil–Petersson Teichmüller space is a
  candidate, and a finite-index subgroup of `B_n` acts on it properly; its
  completion is CAT(0), but the action on the completion has infinite point
  stabilizers (sources to verify).

Known: true for `n <= 7`, because a geometric action is a proper action on a
proper space (route `braid-proper-cat0-action-from-geometric-action`).

## Attempts

- Without cocompactness, isometries need not be semisimple, so the
  translation-length obstructions in `some-braid-group-is-not-cat0` do not
  apply to this claim. A negative answer would need an obstruction to proper
  actions with parabolic elements, for which no candidate is known.
- A positive answer for all `n` could come from a proper but non-cocompact
  space built from the Garside structure (e.g. a CAT(0) metric on an
  infinite-type complex), which would not need the finite link checks of the
  orthoscheme route.
