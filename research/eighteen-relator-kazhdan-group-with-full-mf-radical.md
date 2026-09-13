---
rg: 2
id: eighteen-relator-kazhdan-group-with-full-mf-radical
kind: claim
title: The eighteen-relator presentation defines a Kazhdan group with full MF radical and no nontrivial finite-dimensional representation
distinct_from:
  explicit-eighteen-relator-nonsofic-group: that is the soficity half of the profile of the same presented group; this is the Kazhdan, MF-radical and representation half, which is logically independent of soficity.
  fp-simple-full-mf-radical-group: that is existence of a finitely presented simple group with full MF radical; this names one presentation, eighteen relators on four generators, with that property and property (T).
  binary-leavitt-all-ranks-full-mf-radical: that is the property profile of the unit group and its matrix groups, given with no presentation; this attaches the profile to an explicit relator list.
---

**ESTABLISHED (2026-09-12, unreviewed)** through
`eighteen-relator-kazhdan-group-with-full-mf-radical-proof`.

Let `Q = <a, b, c, x | 18 relators>` be the group of
`thompson-steinberg-presentation-of-leavitt-unit-group`. Then:
- `Q` has Kazhdan's property (T);
- `Rad_MF(Q) = Q`: every homomorphism from `Q` to an MF group is trivial;
- every finite-dimensional linear representation of `Q` over any field is trivial;
- `Q` is simple and not sofic (`explicit-eighteen-relator-nonsofic-group`).

This is the mandate's "explicit non-MF group with short relators". It has four generators;
eliminating `c` by Tietze would give three generators with the same eighteen relators, at the
cost of longer words.
