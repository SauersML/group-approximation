---
rg: 2
id: zaremsky-3-01-aut-torelli-resolved
kind: claim
title: "Decide whether the IA-automorphism group IA_n of F_n is finitely presented for all large n"
---

Part of Zaremsky Problem 3.1 (`zaremsky-3-01-torelli-groups-finitely-presented`).
Let `IA_n = ker(Aut(F_n) -> GL_n(Z))`. This claim is the question for this family.
It is established by exactly one of two routes:

- **Yes**: `zaremsky-3-01-aut-by-yes` requires `ia-automorphism-groups-fp-for-large-rank`.
- **No**: `zaremsky-3-01-aut-by-no` requires
  `ia-automorphism-groups-not-fp-for-infinitely-many-ranks`.

As a bare disjunction this is a classical tautology. Its content is knowing which
disjunct holds, so no `requires: []` route may be written into this claim.
