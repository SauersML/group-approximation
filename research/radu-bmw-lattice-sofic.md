---
rg: 2
id: radu-bmw-lattice-sofic
kind: claim
title: Radu's non-residually-finite BMW lattice is sofic
root: true
distinct_from:
  radu-bmw-lattice-nonsofic: that is the negation.
  titz-witzel-kernel-sofic: that is soficity of the simple Kazhdan building lattice containing this group; this is soficity of the product-of-trees subgroup alone, which is necessary for that claim and much weaker.
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
---

**OPEN.**  Let `Gamma_R` be the six-involution BMW group of
`radu-bmw-lattice-embeds-in-titz-witzel-kernel`.  Eliminating `b = zaz` and
`c = yby` gives

```text
Gamma_R = <a,x,y,z | a^2,x^2,y^2,z^2,(ax)^2,(ay)^2,(zazx)^2, yzazy x yzazy z>.
```

The claim is that `Gamma_R` is sofic.  Marked as a root: soficity of
non-residually-finite irreducible lattices in products of trees is a
standing open question.  Cornulier (arXiv:0906.3374, p. 4) records the
Burger--Mozes groups as not elementary sofic with soficity "unknown".  This
is an explicit small instance, and it is necessary for
`titz-witzel-kernel-sofic`.

Any sofic approximation separates the mark `(xz)^4`, which lies in the
finite residual.

## Attempts

* **Through the Titz--Witzel kernel.**  `radu-bmw-lattice-sofic-from-titz-witzel-kernel`
  derives this claim from `titz-witzel-kernel-sofic`, which is harder.
* **Pull back the horizontal tree group.**  Dead:
  `radu-horizontal-projection-kills-delta-squared` shows that `(xz)^2` acts
  trivially on the horizontal tree, so every almost action pulled back from
  that quotient collapses the mark.
* **Necessary shape of a construction.**  By
  `radu-mark-is-controlled-by-one-commutator`, a marked approximate solution
  must keep `[y(xz)^2y, xz]` macroscopically nontrivial.
