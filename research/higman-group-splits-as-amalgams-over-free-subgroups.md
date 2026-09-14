---
rg: 2
id: higman-group-splits-as-amalgams-over-free-subgroups
kind: claim
title: Higman's four-generator group is two amalgams of sofic Baumslag--Solitar pairs over rank-two free groups
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

Let `H = <a,b,c,d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2>`, with `x^y = y^(-1) x y`. Let
`G_1 = <a,b,c>`, `G_2 = <c,d,a>`, `G_3 = <b,c,d>`, `G_4 = <d,a,b>`, each presented by the two relations of
`H` among its letters. Then:

* `G_1 = BS(a,b) *_<b> BS(b,c)`, and likewise for `G_2, G_3, G_4`; each `G_i` is sofic;
* `{a,c}` freely generates a free subgroup `F_ac` of `G_1` and of `G_2`, and `{b,d}` freely generates a free
  subgroup `F_bd` of `G_3` and of `G_4`;
* `H = G_1 *_(F_ac) G_2 = G_3 *_(F_bd) G_4`.

The freeness comes from the normal form theorem for amalgams: nonzero powers of a stable letter and
nonzero powers of a base letter avoid the amalgamated cyclic subgroup. Soficity of the `G_i` uses the
literature input that amalgams of sofic groups over amenable subgroups are sofic.

**ESTABLISHED 2026-09-12** by `higman-group-amalgam-splittings-proof`.
