---
rg: 2
id: zaremsky-3-01-surface-torelli-resolved
kind: claim
title: "Decide whether the Torelli group of the closed genus g surface is finitely presented for all large g"
---

Part of Zaremsky Problem 3.1 (`zaremsky-3-01-torelli-groups-finitely-presented`).
Let `I_g = ker(Mod(S_g) -> Sp_{2g}(Z))` for the closed oriented surface `S_g`.
This claim is the question for this family. It is established by exactly one of
two routes:

- **Yes**: `zaremsky-3-01-surface-by-yes` requires
  `surface-torelli-groups-fp-for-large-genus`.
- **No**: `zaremsky-3-01-surface-by-no` requires
  `surface-torelli-not-fp-for-infinitely-many-genera`.

As a bare disjunction this is a classical tautology. Its content is knowing which
disjunct holds, so no `requires: []` route may be written into this claim.
