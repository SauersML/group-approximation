---
rg: 2
id: finite-symmetry-equivariant-edge-has-one-holonomy
kind: claim
title: One equivariant HNN edge has one multiplicity holonomy on every symmetry orbit
distinct_from:
  finite-group-shared-overlap-polar-alignment: that aligns two exactifications on one finite subgroup but permits a new commutant unitary on every edge; this uses one semidirect edge and one stable word for a whole finite symmetry orbit.
  three-chart-affine-clifford-return-incidence: that must construct the specific S3-equivariant reset edge and connect its orbit marginals to the three radical failure laws; this proves the general finite-symmetry mechanism once such an edge exists.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that gives a stationary type vector for every graph of finite groups; this controls the two-cell holonomy word but does not by itself create a contextual failure or exclude the regular flow.
---

Let a finite group `H` act by automorphisms on finite groups `E` and `E'`,
and let `phi:E->E'` be an injective `H`-equivariant homomorphism.  Extend it
to

```text
Phi:E semidirect H -> E' semidirect H,
Phi(e,h)=(phi(e),h).                                      (FSE1)
```

Place both semidirect products in a base group and adjoin **one** stable
letter `t` with

```text
t^(-1) x t=Phi(x),       x in E semidirect H.            (FSE2)
```

Then every comparison belonging to the `H` orbit of one edge is implemented
by the same word `t`.  In particular, if `p` is any spectral projection in a
finite group-algebra packet of `E`, put

```text
p_h=h p h^(-1),
q= t^(-1) p t,
q_h=h q h^(-1).                                         (FSE3)
```

The relations `(FSE2)` include `[t,h]=1`, so exactly

```text
t^(-1) p_h t=q_h.                                       (FSE4)
```

After decomposing an exact finite-dimensional edge representation into
irreducibles, the stable letter may still contain an arbitrary unitary on
each multiplicity space, but it is **one common unitary** for the whole
`H` orbit.  There are no independently selectable orbit-edge rotations.

The same conclusion is dimension-independently robust.  For fixed `E,H`,
finite-group HS exactification followed by polar alignment gives a constant
`C_(E,H)` such that a unitary tuple of relator energy `mathcal E` satisfies

```text
||t^(-1) p_h t-q_h||_2 <= C_(E,H) sqrt(mathcal E)       (FSE5)
```

simultaneously for every `h`.  Hence every scalar joint law made from a pair
of likewise conjugated source and endpoint events has the same orbit
marginal up to `O(sqrt(mathcal E))`, by unitary invariance and
`|tr(A)|<=||A||_2`.

This is exactly the amount of holonomy synchronization absent from three
unrelated graph-of-groups edges.  It is not by itself a nonhyperlinearity
obstruction: the endpoint success/failure conventions must also be an
`H`-orbit of word-defined events coupled to the global contextual system.
