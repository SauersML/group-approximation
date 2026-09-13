---
rg: 2
id: zaremsky-2-14-boone-higman-conjecture
kind: claim
title: "Zaremsky Problem 2.14 resolved: is the Boone--Higman conjecture true?"
root: true
distinct_from:
  boone-higman-conjecture: that claim is the affirmative statement that every finitely generated group with solvable word problem embeds in a finitely presented simple group; this is Zaremsky's Problem 2.14 as a question, established by either answer, and it also covers the converse direction
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 14,
verbatim: "Boone–Higman Conjecture: A finitely generated group has solvable
word problem iff it embeds in a finitely presented simple group. (I put this
in the “Thompson groups” section since a resolution to this conjecture would
presumably come from the world of Thompson-like groups.)"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-14-by-boone-higman` requires `boone-higman-conjecture`
  (the forward direction) and `subgroups-of-fp-simple-groups-have-solvable-wp`
  (the converse, Kuznetsov's theorem).
- **No**: no negation claim is on main as of 2026-09-13. A negative answer
  lands as a claim that some finitely generated group with solvable word
  problem embeds in no finitely presented simple group, with its own route
  into this root.

Never write a `requires: []` route into this claim.

**Reading.** The "iff" has a classical half: a finitely generated subgroup of
a finitely presented simple group has solvable word problem. So the open
content of Problem 2.14 is exactly `boone-higman-conjecture`.

**Ownership.** The Boone--Higman region (`boone-higman-conjecture` and its
~220 nodes) belongs to a live peer campaign. This root only wires Zaremsky's
problem to that goal. The research happens there.
