---
rg: 2
id: leavitt-unit-groups-mod-scalars-satisfy-pbh
kind: claim
title: For every prime p the finitely presented simple group L_(F_p)(1,2)^× / F_p^× admits an action of type (A), so it and all its subgroups satisfy permutational Boone--Higman
distinct_from:
  binary-leavitt-unit-group-satisfies-pbh: that is the case p = 2, established through the Cantor module extension; this covers every prime p, and it does so with an action of the group itself.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 for all finitely presented simple groups; this answers it for the groups L_(F_p)(1,2)^× / F_p^×.
  leavitt-units-act-two-transitively-on-chen-module-lines: that is the transitivity and stabilizer computation; this is the permutational Boone--Higman conclusion drawn from it.
---

**ESTABLISHED** through `leavitt-units-pbh-via-chen-module-line-action` (not
independently reviewed; no novelty is claimed).

Let `p` be a prime and `G_p = L_(F_p)(1,2)^× / F_p^×`. Then:
- `G_p` acts on the lines of the Chen module `F_p[D]` of the tail class of `0^∞`, and
  this action is of type (A);
- so `G_p`, and every subgroup of `G_p`, embeds in a group admitting an action of type
  (A).

**Consequences.**
- **BFFHZ Theorem C.** `G_p` embeds in a finitely presented simple highly transitive
  group, and in a finitely presented simple MIF group
  (`fp-simple-highly-transitive-groups-satisfy-pbh`). So BFFHZ Question 3.4 has a
  positive answer for these finitely presented simple groups.
- **The binary case.** For `p = 2` this reproves `binary-leavitt-unit-group-satisfies-pbh`
  without the Cantor-module extension (`binary-leavitt-pbh-via-chen-module-lines`).
- **Trust surface.** The imported finite presentation of `G_p` rests on Khanh
  arXiv:2609.08428v1 and Ara--Cortiñas arXiv:1108.0352v3, as recorded in
  `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`.
