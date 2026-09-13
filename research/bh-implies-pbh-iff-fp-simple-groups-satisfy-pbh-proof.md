---
rg: 2
id: bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh-proof
kind: route
title: Apply BFFHZ Theorem C to finitely presented simple groups
target: bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh
requires:
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - simple-envelope-forces-solvable-word-problem
---

Numbering as in the target.

**(1) ⟹ (2).** Let `S` be finitely presented and simple. It is finitely
generated, and it has solvable word problem by
`simple-envelope-forces-solvable-word-problem` (Kuznetsov's argument). It
satisfies BH trivially, through the identity embedding. By (1), `S` satisfies
PBH.

**(2) ⟹ (1).** Let `G` be finitely generated with solvable word problem and
suppose `G` embeds in a finitely presented simple group `S`. By (2), `S` embeds
in a group `Γ` with an action of type (A). The composite embedding `G ≤ S ≤ Γ`
shows that `G` satisfies PBH.

**(2) ⟺ (3) ⟺ (4).** Fix a finitely presented simple `S`. It is finitely
generated with solvable word problem, as above, so BFFHZ Theorem C applies to it
(`fp-simple-highly-transitive-groups-satisfy-pbh`):
- `S` satisfies PBH (their (i));
- iff `S` embeds in a finitely presented simple highly transitive group (their
  (iii));
- iff `S` embeds in a finitely presented simple MIF group (their (iv)).

Quantifying over all finitely presented simple `S` gives (2) ⟺ (3) ⟺ (4).

Nothing beyond Theorem C and solvability of the word problem in finitely
presented simple groups is used.
