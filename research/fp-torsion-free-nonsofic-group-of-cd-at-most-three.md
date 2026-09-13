---
rg: 2
id: fp-torsion-free-nonsofic-group-of-cd-at-most-three
kind: claim
title: A finitely presented torsion-free nonsofic group of cohomological dimension at most three
distinct_from:
  fournier-facio-group-is-nonsofic: that is a finitely presented torsion-free nonsofic group containing the wreath shift S wr Z, so its cohomological dimension is infinite; this one has cohomological dimension at most three.
  kun-thom-double-of-hyperbolic-pair-has-finite-cd: that is a finitely generated torsion-free nonsofic double of finite, uncontrolled dimension over a hyperbolic cover; this uses the dimension-two graphical cover, which gives finite presentation and the bound three.
  integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic: that is a torsion-free nonsofic lamp wreath, of infinite dimension; this is an amalgam with no lamps.
---

**ESTABLISHED (unreviewed).** Let `G` be the Ollivier--Wise graphical Rips cover of
`R^x = L_(F_2)(1,2)^x`, and `Gamma_hat <= G` the pulled-back Leavitt subgroup of
`cd-two-group-with-infranormal-kazhdan-pair`. The double

```text
D = G *_(Gamma_hat) G
```

is finitely presented, torsion-free, not sofic, and `cd D <= 3`.

**Why it is worth recording.**
- It bounds the dimension. The double over the Belegradek--Osin cover
  (`kun-thom-double-of-hyperbolic-pair-has-finite-cd`) is also nonsofic of finite dimension, but
  that dimension is not controlled. Here it is at most three.
- Its certificate is Kun--Thom Theorem A, the one recorded certificate not excluded in finite
  dimension by `kazhdan-compression-instances-have-infinite-vcd`.
- Its dimension is exactly three. `compressed-doubles-raise-cohomological-dimension` (DB1) gives
  `cd D >= 3`.
- For roots that ask for nonsofic groups of dimension two (`nonsofic-one-relator-group`,
  `nonsofic-one-vertex-square-complex-group`, `titz-witzel-kernel-nonsofic`), doubles cannot close
  the last dimension: by (DB1), every double over a compressed Kazhdan subgroup has dimension at
  least three.

**Model tests.**
- The double of `SL_3(Z)` over the normal subgroup `1` is sofic, so non-normality is used.
- Lamp wreath products over the same pair are nonsofic but of infinite dimension, so the double
  is what gives the bound.

Novelty was checked only against this graph; no web or arXiv search was possible this session.

Proof: `fp-torsion-free-nonsofic-group-of-cd-at-most-three-proof`.
