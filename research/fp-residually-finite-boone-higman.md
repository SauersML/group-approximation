---
rg: 2
id: fp-residually-finite-boone-higman
kind: claim
root: true
title: Every finitely presented residually finite group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over every finitely generated group with solvable word problem; this only over finitely presented residually finite groups, which have solvable word problem, so it is a strictly weaker open problem that the conjecture implies.
  decidable-fp-groups-need-not-embed-in-rational-group: that excludes one kind of host for some finitely presented residually finite inputs; this asks for a finitely presented simple host of any kind for all of them.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**OPEN.** Every finitely presented residually finite group `G` embeds in a
finitely presented simple group.

This is item (12) of Problem 5.3 in Belk--Bleak--Matucci--Zaremsky,
*Progress around the Boone--Higman conjecture*: "Prove the Boone--Higman
conjecture for ... (12) Finitely presented residually finite groups." The
survey's Remark 5.4 records later progress on items (1)--(4), (8) and (13),
not on item (12).

It is a special case of `boone-higman-conjecture`, by
`fp-rf-boone-higman-from-boone-higman`. It is a root because it is a named
open problem in its own right, and because the residually finite case has a
sufficient route that does not exist for general inputs:
`fp-rf-boone-higman-via-fp-self-similar-overgroups`.

## What the known theorems already cover

Among residually finite inputs, Boone--Higman is known for finitely presented
self-similar groups and their subgroups
(`fp-self-similar-groups-embed-in-fp-simple-groups`), for finitely generated
subgroups of `GL_n(Q)` (same source, Theorem 1.2), and for hyperbolic groups
that are residually finite (Belk--Bleak--Matucci--Zaremsky). The finitely
presented residually finite groups of Kharlampovich--Myasnikov--Sapir with
algorithmically complex word problem are not covered by any of these classes.

## Attempts

1. **Finitely presented self-similar overgroups.** Wired as
   `fp-rf-boone-higman-via-fp-self-similar-overgroups`. The open clause is
   `every-fp-rf-group-embeds-in-fp-self-similar-group`.
2. **Finite-state hosts.** *Dies* for some inputs:
   `decidable-fp-groups-need-not-embed-in-rational-group` produces a
   finitely presented residually finite input embedding in no rational
   homeomorphism group, so automaton groups and contracting rational
   similarity groups cannot handle every input.
3. **Hosts with a uniform complexity bound.** *Dies as a universal method*:
   `complexity-bounded-host-classes-are-not-universal` shows that no class of
   groups whose word problems share one recursive time bound contains every
   decidable input. A successful construction for complex residually finite
   inputs must output groups with complex word problem.
4. **The profinite translation action.** `G` acts faithfully by translation
   on its profinite completion, a Cantor space. Each orbit carries the regular
   action, which has infinitely many orbits of pairs, so this action supplies
   no type (A) action and no route through
   `type-a-action-gives-boone-higman-for-subgroups`. Recorded in prose only.
