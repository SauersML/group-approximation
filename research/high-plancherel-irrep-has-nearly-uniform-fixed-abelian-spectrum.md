---
rg: 2
id: high-plancherel-irrep-has-nearly-uniform-fixed-abelian-spectrum
kind: claim
title: A high-Plancherel irreducible has nearly uniform spectrum on every fixed elementary abelian subgroup
distinct_from:
  canonical-finite-packet-data-stop-at-scalar-overlaps: that says scalar packet data leave reservoir ownership free; this gives a quantitative restriction on literal commuting subgroup observables inside one high-mass irreducible block.
  affine-frobenius-group-has-almost-full-simple-block: that constructs a block with Plancherel mass tending to one; this explains why arbitrary predicates in that block must use nonliteral group-algebra observables.
  standard-type-thin-common-reflection-sector: that uses a particular literal reflection inside a low absolute-mass type; this concerns absolute Plancherel mass tending to one.
---

Let `rho` be an irreducible representation of a finite group `K`, with
character `chi`, dimension `d`, and Plancherel mass

```text
alpha=d^2/|K|.                                         (HPM1)
```

For a fixed subgroup `E=(C2)^k`, let `m_psi` be the multiplicity of the sign
character `psi` in `rho|_E`.  Then

```text
|m_psi/d-1/|E||
 <=sqrt((|E|-1)(1-alpha)/alpha)/|E|.                  (HPM2)
```

In particular, if `alpha>1-1/|E|`, every sign character occurs.  As
`alpha->1`, the literal commuting involutions from `E` have asymptotically
uniform joint sign spectrum.  They therefore cannot realize an arbitrary
sparse Boolean predicate inside a very high-Plancherel primitive block.

This does not limit arbitrary matrices in the block.  It explains the role
of the Frobenius packet: high density and arbitrary local predicate support
are compatible only when the logical observables are general group-algebra
elements rather than literal commuting group elements.

