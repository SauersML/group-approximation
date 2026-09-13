---
rg: 2
id: simple-kazhdan-universal-host-centralizer-proof
kind: route
title: Apply cyclic-corner universality in the multiplicity centralizer of a prescribed finite subgroup
target: simple-kazhdan-universal-host-has-rich-finite-centralizers
requires:
  - simple-kazhdan-lef-hosts-all-countable-locally-finite
  - universal-odometer-corners-preserve-kazhdan-hosts
  - cyclic-tower-centralizers-contain-elementary-wreath-products
artifacts:
  - research/artifacts/pestov91-universal-host-finite-centralizers-2026-09-13.md
---

Choose the fixed host and core of the universal-host construction. A
three-element torsion marking for this same host is supplied by the
required universal-host claim and its binary generator proof. A
finite subgroup `F` of their increasing core is contained in some
`SL_(3N)(F_2)`, `N=j!`. Refine to level `3rN`. The corner claim supplies
the infinite simple Kazhdan LEF universal group `H=EL_3(A)`, and the
matrix-centralizer claim embeds `W=H^r semidirect Sym(r)` into `C_S(F)`.
Since `H` is nontrivial and centreless, `W` is centreless: a central
element cannot move a factor, and then each of its components is central
in `H`. Thus `F intersect W <= Z(W)=1`, so multiplication embeds the
direct product and fixes `F`. The proof artifact records the exact
coordinate refinement and all injectivity checks.
