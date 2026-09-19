---
rg: 2
id: good-groups-have-no-persistent-finite-cohomology
kind: claim
title: Every positive-degree finite-coefficient class on a good group dies on a finite-index subgroup
distinct_from:
  persistent-degree-two-class-on-hyperbolic-group: that asks for one residually finite hyperbolic group carrying a class that survives every finite-index subgroup; this proves such a candidate cannot be good, and in particular cannot be hyperbolic virtually special.
---

Let `G` be good in Serre's sense. Let `M` be a finite `G`-module, let `q>0`,
and let `alpha in H^q(G;M)`. There is a finite-index normal subgroup
`G_0 normal G` such that

```text
res^G_(G_0)(alpha) = 0.
```

Equivalently, the directed colimit of positive-degree finite-coefficient
cohomology over finite-index subgroups, with transition maps given by
restriction, is zero.

In particular, every hyperbolic virtually special group has this property.
Therefore any witness to
[[persistent-degree-two-class-on-hyperbolic-group]] must be non-good and
cannot be hyperbolic virtually special.

**Primary sources.** Robert Kropholler and Gareth Wilkes, *Profinite
properties of RAAGs and special groups*, Bull. Lond. Math. Soc. **48**
(2016), 1001--1007, DOI `10.1112/blms/bdw056`, arXiv:`1603.07197`,
definition of goodness and Theorem 9; Nicolas Bergeron and Akshay Venkatesh,
*The asymptotic growth of torsion homology for arithmetic groups*, J. Inst.
Math. Jussieu **12** (2013), 391--447, DOI
`10.1017/S1474748012000667`, arXiv:`1004.1083`, Section 8.5. Sources checked
2026-08-30.
