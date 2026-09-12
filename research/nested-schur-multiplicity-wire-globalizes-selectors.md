---
rg: 2
id: nested-schur-multiplicity-wire-globalizes-selectors
kind: claim
title: A literal nested Schur multiplicity wire globally commutes all past and future selectors
distinct_from:
  schur-rank-output-is-not-a-scalar-selector: that rules out naming one nonlinear output by a scalar word; this shows that placing the next packet on the literal residual multiplicity space also has a contextuality cost.
  context-local-schur-packet-marked-extension: that preserves contextuality by imposing no cross-context packet relations; this identifies the cross-level relation which destroys that protection.
---

Let a Schur packet `A_f<=B_f` act exactly on a Hilbert space and suppose a
next packet algebra is required to act on the external multiplicity space of
the `A_f`-decomposition. Then the next packet commutes with `A_f`. Since every
input selector `z_i` lies in the center of `A_f`, every generator—and in
particular every selector—of the next packet commutes with every current
`z_i`.

Iterating a literal residual-multiplicity construction therefore forces

```text
[z_(n,i),z_(m,j)]=1        for every connected pair of levels n<m. (NSG1)
```

If the transported selector family covers the contexts of the source BCS,
the resulting exact representation factors through its globally commuting
quotient. Hence such a construction cannot be used without proving that the
marked completeness model survives that quotient. A contextual Schur tape
must instead reset/forget the old selector center while retaining only the
branch multiplicity, or use a partial-center/projective holonomy which never
puts the entire next packet in the old commutant.

