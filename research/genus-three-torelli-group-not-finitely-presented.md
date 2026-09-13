---
rg: 2
id: genus-three-torelli-group-not-finitely-presented
kind: claim
title: "The Torelli group of the closed genus three surface is not finitely presented"
---

`I_3 = ker(Mod(S_3) -> Sp_6(Z))` is not finitely presented.

This is a single-genus partial claim for Zaremsky Problem 3.1. It does not decide
`surface-torelli-not-fp-for-infinitely-many-genera`, but `g = 3` is the first open
genus, and it is the only one with published evidence pointing to a direction.
`I_3` is finitely generated (`surface-torelli-fg-in-genus-at-least-three`), has
`cd(I_3) = 4`, and has `H_4(I_3; Z)` infinitely generated (Bestvina–Bux–Margalit,
arXiv:0709.0287, Theorem A and abstract). Gaifullin's Theorem A
(`surface-torelli-second-homology-finitely-generated`) needs `g >= 4`, so it does
not cover `H_2(I_3; Z)`.

The route `genus-three-torelli-not-fp-via-infinite-second-homology` reduces this
claim to `genus-three-torelli-second-homology-infinitely-generated`.

## Attempts

- 2026-09-13 (lane z3-01-torelli): through second homology, on the prerequisite
  claim; see that claim's Attempts for where it stands (the differential `d^3`).
- A no-answer that avoids `H_2` would need a relation-module or non-homological
  argument. None is known.
