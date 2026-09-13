---
rg: 2
id: kun-thom-double-of-hyperbolic-pair-has-finite-cd
kind: claim
title: The Kun--Thom double of the hyperbolic Leavitt cover pair is a torsion-free nonsofic group of finite cohomological dimension
distinct_from:
  integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic: that is the integer-lamp wreath over the same pair, whose lamp group Z^(infinity) forces infinite cohomological dimension; this is the double over the pair, which stays in finite dimension.
  kt-pair-group-double-is-nonsofic: that imports Kun--Thom Theorem A for doubles of infranormal Kazhdan pairs, with instances from Theorem E that have unbounded finite subgroups; this applies it to a pair inside a torsion-free hyperbolic group and computes the dimension.
  kazhdan-compression-instances-have-infinite-vcd: that shows the compression criterion and lamp wreaths never fire in finite virtual cohomological dimension; this shows the double does fire there, so finite dimension alone is not a fence against Kun--Thom certificates.
---

**ESTABLISHED (unreviewed).**
- Let `N <= Gamma_hat <= G_hat <= G` be the rigid pair of
  `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`, inside the torsion-free
  word-hyperbolic Kazhdan cover `G` of the binary Leavitt unit group
  (`hyperbolic-kazhdan-cover-of-leavitt-unit-group`).
- Put `D = G_hat *_(Gamma_hat) G_hat`.

Then:

```text
D is finitely generated, torsion-free and not sofic, and cd D <= cd G + 1 < infinity.
```

So there is a nonsofic group of finite cohomological dimension. Its subgroups contain no `Z^n` for
`n > cd G + 1`, and no nontrivial finite group.

**What it shows about fences.**
- The commuting-factor criterion and lamp wreath products never fire in finite virtual
  cohomological dimension (`kazhdan-compression-instances-have-infinite-vcd`). Theorem A doubles
  do.
- In torsion-free dimension two even doubles are excluded: a double over a Kazhdan pair has
  dimension at least three (`compressed-doubles-raise-cohomological-dimension`). The dimension of
  this `D` is not controlled from above, since `G` is built
  over a lattice in `Sp(2,1)`. `fp-torsion-free-nonsofic-group-of-cd-at-most-three` uses the
  Ollivier--Wise cover instead, which gives finite presentation and dimension at most three.
- `G_hat` is in fact all of `G`: the nine-leaf group is the whole unit group (see the proof of that
  node). So this `D` is finitely presented as well.

**Credit and status.** The pair, the cover and Theorem A are all in the graph. The only new step
is the dimension count. It has not been reviewed, and no literature check was possible in this
session.

Proof: `kun-thom-double-of-hyperbolic-pair-has-finite-cd-proof`.
