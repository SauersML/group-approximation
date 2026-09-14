---
rg: 2
id: cckw-question-mark-triangle-groups-virtually-torsion-free
kind: claim
title: Eighteen hyperbolic trivalent triangle groups tabulated with VTF "?" by Caprace–Conder–Kaluba–Witzel are virtually torsion-free
distinct_from:
  hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free: that asks for a hyperbolic triangle of finite groups with no finite quotient injective on its vertex groups; this exhibits such quotients for eighteen explicit literature members, so none of them is an example
  triangle-of-groups-half-girth-structure: that imports Theorem 3.1 of Caprace–Conder–Kaluba–Witzel, whose (iv) turns a vertex-injective finite quotient into virtual torsion-freeness; this supplies the quotients for specific groups
---

Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, §"Tables", list the trivalent triangle groups
`G = <a,b,c | a^3, b^3, c^3, R_ab, R_bc, R_ca>`. The vertex groups `<a,b>`, `<b,c>`, `<c,a>` have order
`3n/2` for link labels `n` and act simply transitively on the edges of cubic link graphs. The table
column `VTF` reads `Yes` or `?`.

**ESTABLISHED (computer-assisted; unreviewed).** The following groups are non-elementary hyperbolic and
virtually torsion-free. In the arXiv source each is tabulated with VTF `?`.
- Half-girth type (3,3,4): `G_4^{14,14,48}`, `G_0^{16,16,48}`, `G_0^{16,16,54}`, `G_0^{16,18,48}`,
  `G_0^{16,24,48}`, `G_2^{16,24,54}`, `G_4^{26,26,48}`.
- Half-girth type (3,4,4): `G_0^{16,40,48}`, `G_0^{18,40,54}`, `G_0^{18,54,54}`, `G_2^{24,48,54}`,
  `G_0^{24,54,54}`, `G_2^{24,54,54}`, `G_2^{26,48,54}`.
- Half-girth type (4,4,4): `G_0^{48,54,54}`, `G_8^{48,54,54}`, `G_0^{54,54,54}`, `G_2^{54,54,54}`.

For each group there is an explicit homomorphism `G -> S_d`, given by the images of `a, b, c`, with two
properties. It satisfies every relator. The images of the vertex groups have orders `3n/2`, so the
homomorphism is injective on them. By Theorem 3.1(iv) its kernel is a torsion-free subgroup of finite index.
- Seventeen of the homomorphisms are products of epimorphisms onto simple quotients that CCKW already list.
- For `G_4^{14,14,48}` the listed quotient `A_7` kills the central involution of the vertex group
  `C3 x SL(2,3)`, and a normal subgroup of index 5040 with quotient `2.A_7` is injective instead.

**What it changes.** These groups drop out as candidates for
`hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free`. After amalgamation into alternating
groups (`simple-vertex-triangles-are-universal-for-triangle-vtf`) they also drop out for
`hyperbolic-simple-triangle-group-without-finite-quotients`. So the table's `?` entries are not all hard
cases. The remaining 56 are listed in the artifact with the kernel intersections that no quotient found
removes.

**Scope of the source check.**
- The `?` entries are those of the arXiv source.
- The published tables (J. London Math. Soc. 106 (2022), Appendices A–C, supplementary material) were
  not read.
- A bounded web search found no later paper settling these entries.

See `cckw-question-mark-triangle-groups-vtf-certificates`.
