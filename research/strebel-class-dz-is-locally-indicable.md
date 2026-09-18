---
rg: 2
id: strebel-class-dz-is-locally-indicable
kind: claim
title: Over a locally indicable group, a homomorphism of free Z[G]-modules is injective when its augmentation is injective
distinct_from:
  flat-weak-bass-holds-exactly-for-locally-indicable-groups: that compares the von Neumann rank with the augmentation rank through the universal Hughes-free division ring, and is itself a proposed result; this is the older import of Strebel's class D(Z) and its identification with the locally indicable groups by Howie--Schneebeli, stated for integral free modules with no division ring.
  howie-locally-indicable-nonsingular-equations-are-solvable: that is Howie's theorem on nonsingular equations over locally indicable groups; this is a homological statement about maps of free group-ring modules.
artifacts:
  - research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md
---

Let `G` be a locally indicable group, and let `f: M -> N` be a homomorphism of free
`Z[G]`-modules. If the induced homomorphism of abelian groups
`f (x) id: M (x)_{Z[G]} Z -> N (x)_{Z[G]} Z` is injective, then `f` is injective.

This is Strebel's property `D(Z)` (Comment. Math. Helv. 49 (1974), p. 305). Its class was
shown by Howie and Schneebeli (Manuscripta Math. 44 (1983)) to be exactly the class of locally
indicable groups.

**Side convention.** The statement is symmetric in the side. The anti-automorphism
`g -> g^{-1}` of `Z[G]` commutes with the augmentation and exchanges left and right free
modules, so the statement for left modules implies the one for right modules.

**ESTABLISHED 2026-09-18** by import, through [[strebel-class-dz-is-locally-indicable-citation]].
