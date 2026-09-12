---
rg: 2
id: radu-bmw-lattice-embeds-in-titz-witzel-kernel
kind: claim
title: Radu's non-residually-finite BMW lattice embeds, up to index four, in the smallest Titz--Witzel kernel
distinct_from:
  titz-witzel-simple-kazhdan-cat0-lattices-exist: that imports the simple Kazhdan C2-tilde lattices themselves; this records the explicit product-of-trees subgroup carrying their non-residual finiteness and its six-generator involutive presentation.
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
---

**ESTABLISHED (literature import).**  Let `Gamma_R` be the BMW group of
Radu's square complex `S_R`.  It acts simply transitively on the vertices of
a product of two 3-regular trees, contains `pi_1(S_R)` with index four, and
has the presentation

```text
Gamma_R = <a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2,
                         axax, ayay, azbz, bxbx, bycy, cxcz>.        (RE1)
```

Then:

1. `Gamma_R` is irreducible and not residually finite.
2. `(xz)^4` lies in the finite residual of `Gamma_R`.  Titz Mite--Witzel
   Remark 3.6 identifies `(xz)^(+-4)` as the shortest such elements.
3. `pi_1(S_R)` embeds in `K = Gamma_1^2`, the smallest simple Titz--Witzel
   kernel, through the subdivided subcomplex spanned by the triangles
   `t_1,...,t_18` of `Y_1^2`.

Consequently `K` sofic implies `Gamma_R` sofic, and `Gamma_R` nonsofic
implies `K` nonsofic (subgroup permanence, and
`sofic-kernel-amenable-quotient-permanence` for the index-four extension).

DERIVATION
radu-bmw-lattice-embeds-in-titz-witzel-kernel-citation
