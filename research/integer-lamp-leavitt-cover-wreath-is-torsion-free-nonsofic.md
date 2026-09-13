---
rg: 2
id: integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic
kind: claim
title: The integer-lamp wreath over the hyperbolic Leavitt cover pair is a finitely generated torsion-free nonsofic group
distinct_from:
  fournier-facio-group-is-nonsofic: that imports a torsion-free nonsofic group from an external preprint; this is a torsion-free nonsofic group derived inside the graph from the hyperbolic Leavitt cover and Kun--Thom normalization.
  kun-thom-wreath-carries-rigid-defect: that is the defect of the binary-lamp wreath over the positive-characteristic Theorem E pair, which has torsion; this uses integer lamps over a torsion-free pair.
---

**ESTABLISHED.**  Let `N <= Gamma_hat <= G_hat <= G` be the rigid pair of
`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`, inside the
torsion-free hyperbolic Kazhdan cover `G` of the binary Leavitt unit group
(`hyperbolic-kazhdan-cover-of-leavitt-unit-group`).  Put

```text
W_hat = (direct_sum_(G_hat/Gamma_hat) Z) x| G_hat .
```

Then `W_hat` is finitely generated, torsion-free and not sofic.

**Structure.**

- `W_hat` is an extension of a free abelian group by a subgroup of a
  torsion-free word-hyperbolic group.
- It contains the infinite Kazhdan groups `N` and `Gamma_hat`.
- Its nonsoficity rests only on graph nodes: the Belegradek--Osin cover,
  the nine-leaf Leavitt pair, and Kun--Thom Theorem 4.1 through
  `sofic-groups-kill-rigid-compression-defects`.
- It does not import Fournier--Facio.

**What it is not known to have.**

- Unique products: `W_hat` has them iff `G_hat` does, and that is open.  A deep
  finite-index version has them if `G` is residually finite
  (`non-rf-hyperbolic-group-or-unique-product-nonsofic-group`).
- Left-orderability: that would need `G_hat` left-orderable, an instance of
  `infinite-left-orderable-kazhdan-group`.

Derivation: `integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic-proof`.
