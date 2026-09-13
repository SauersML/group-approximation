---
rg: 2
id: every-type-fpn-group-is-of-type-fhn-via-acyclic-kernels
kind: route
title: "FP_n implies FH_n if every FP_n group is a type F_{n-1} group modulo an (n-1)-acyclic normal subgroup"
target: every-type-fpn-group-is-of-type-fhn
requires:
  - every-type-fpn-group-is-fn-minus-1-group-mod-acyclic-subgroup
  - fn-groups-mod-acyclic-normal-subgroups-are-type-fhn
---

Given `G` of type `FP_n`, the first prerequisite supplies `Q` of type
`F_{n−1}` and `Q ↠ G` with `(n−1)`-acyclic kernel. The second then gives a
free cocompact `(n−1)`-acyclic `G`-complex.

Honesty note. At `n = 3` the prerequisite is *equivalent* to the target
(`type-fh3-iff-fp3-and-superperfect-kernel-over-fp-group`). At general `n`
the converse is expected through a finite Kan–Thurston theorem, which has
not been checked. So this route translates Problem 1.4 into group theory
(finite presentations and acyclic kernels) rather than reducing it to
something weaker.
