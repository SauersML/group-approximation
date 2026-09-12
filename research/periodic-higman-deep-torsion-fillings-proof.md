---
rg: 2
id: periodic-higman-deep-torsion-fillings-proof
kind: route
title: Fill the primitive stable letter while protecting the base mark
target: periodic-higman-deep-torsion-fillings
requires:
  - periodic-higman-mapping-torus-is-word-hyperbolic
---

The injective ascending HNN extension `M_phi` is torsion-free.  Its height map

```text
M_phi->Z,             t |-> 1,             F |-> 0
```

shows that `t` is primitive.  In a torsion-free hyperbolic group this makes
the maximal elementary subgroup containing `t` equal to `<t>`.

Apply the hyperbolically embedded cyclic filling theorem to `<t>` while
protecting the finite set `{a}`.  For every sufficiently deep subgroup
`<t^m>`, the filling map is injective on `{a}` and the quotient is hyperbolic
relative to the finite peripheral image `<t>/<t^m>`.  A group hyperbolic
relative to a finite subgroup is word-hyperbolic.  This supplies one threshold
`m_0` with both asserted properties.  The input is the standard
rotating-family/Dehn filling theorem of Dahmani--Guirardel--Osin,
arXiv:1111.7048.
