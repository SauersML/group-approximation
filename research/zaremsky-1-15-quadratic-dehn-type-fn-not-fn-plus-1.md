---
rg: 2
id: zaremsky-1-15-quadratic-dehn-type-fn-not-fn-plus-1
kind: claim
title: "Zaremsky Problem 1.15 resolved: for each n >= 2, is there a group of type F_n but not F_{n+1} with quadratic Dehn function?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 15,
verbatim: "Find finitely presented groups `G_n` (`n ≥ 2`) with quadratic Dehn
function such that `G_n` is of type `F_n` but not `F_{n+1}`. (E.g., do
Bieri–Stallings groups all have quadratic Dehn function?) [Actually this isn't
open, it was proved by Carter and Forester using Bieri–Stallings groups.]"

This claim is the question. It is established only through an answer route:

- **Construction**: `zaremsky-1-15-by-stallings-bieri` requires
  `stallings-bieri-groups-have-quadratic-dehn-function`.

Never write a `requires: []` route into this claim.

**Reading.** For every `n ≥ 2` the problem asks for a finitely presented group
`G_n` with quadratic Dehn function that is of type `F_n` but not of type
`F_{n+1}`. The parenthetical asks whether every Stallings--Bieri group `SB_m`
has quadratic Dehn function. A Dehn function is defined only for finitely
presented groups, so this concerns `m ≥ 3`, since `SB_1` and `SB_2` are not
finitely presented. For those the answer is yes.

**Status.** Answered in the list's own note, by Carter and Forester
(arXiv:1509.07539).
