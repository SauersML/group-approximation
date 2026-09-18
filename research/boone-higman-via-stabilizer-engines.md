---
rg: 2
id: boone-higman-via-stabilizer-engines
kind: route
title: Put the input in a finitely generated decidable simple group S, then take the derived full group of Z/2 * S on its compactified Bass–Serre tree
target: boone-higman-conjecture
requires:
  - boone-higman-thompson-simple-envelope
  - simple-inputs-have-finitely-presented-stabilizer-engines
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
---

Let `G` be finitely generated with solvable word problem.

1. **A decidable simple envelope.** By `boone-higman-thompson-simple-envelope`, `G`
   embeds in an infinite finitely generated computably presented simple group `S`.
   `S` has solvable word problem, being recursively presented and simple (Kuznetsov).
2. **The engine contains `S`.** In `F_S`, the full group of `Z/2 * S` on its compactified
   Bass–Serre tree, `S` is the isotropy of a vertex point. `S` is perfect, so its image in
   the abelian group `(F_S)_ab` is trivial, and `S ≤ D(F_S)`. `D(F_S)` is simple
   (`free-product-boundary-groupoids-carry-the-vertex-group-homology`).
3. **Finite presentation.** `D(F_S)` is finitely presented by the open
   `simple-inputs-have-finitely-presented-stabilizer-engines`. So
   `G ≤ S ≤ D(F_S)`, a finitely presented simple group. `∎`

**Status. CIRCULAR (2026-09-18).** Step 3 is refuted as stated
(`stabilizer-engines-of-non-fp-simple-groups-are-not-fp`). It can hold for an envelope `S` only if
`S` is already finitely presented (`fp-stabilizer-engines-need-fp-vertex-groups`), and then `S` itself
is the finitely presented simple overgroup. The live route is `boone-higman-via-fp-stabilizer-engines`.
Historical notes:
- The necessary side is proved: a finitely presented engine forces a decidable vertex
  group (`fp-stabilizer-engines-need-decidable-vertex-groups`).
- The first test case, `B = Z` (Reid's group), is itself open.
