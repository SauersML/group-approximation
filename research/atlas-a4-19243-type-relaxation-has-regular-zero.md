---
rg: 2
id: atlas-a4-19243-type-relaxation-has-regular-zero
kind: claim
title: The exact A4 and collision-19243 type-profile relaxation contains the regular zero-defect point
distinct_from:
  atlas-a4-19243-classical-collapse: that excludes the sixty regular A8 automorphism alignments; this proves that their common regular multiplicity profile remains feasible once holonomy and common-frame data are forgotten.
  atlas-19243-has-continuous-regular-s3-line-holonomy: that constructs the local continuous collision family; this glues its finite-subgroup type coordinates to the full thirty-context A4 flow polytope.
  atlas-a4-context-type-vector-converges-to-regular-point: that shows canonical sequences approach the regular A4 type point; this decides whether that point is excluded by the collision type constraints.
---

Use raw normalized multiplicity coordinates

```text
z_(v,pi)=multiplicity of pi at vertex v / common dimension D.
```

For every incidence `e:H->G` in the two `A8` charts, thirty `A4` contexts,
and their `C2/C3` edges, let `R_e` be the integral irreducible-restriction
matrix.  The exact compatible A4 type polytope is

```text
P_A4={z>=0:
       R_e z_G=z_H for every incidence e,
       sum_(pi in Irr(G)) dim(pi) z_(G,pi)=1
       for every vertex G}.                           (ATP1)
```

The collision type relaxation adjoins an exact representation of the relative
collision presentation, identifying its `S3=<r,s>` marginal with the relevant
packet restriction and identifying the spectral multiplicities of its
involution `c` with those of a chart transvection.

This fibered type relaxation contains the following rational point.  At every
finite-group vertex `H`, including the two chart vertices and all packet
subgroups, put

```text
z_(H,pi)=dim(pi)/|H|.                                  (ATP2)
```

Thus each A8 chart has its Plancherel/regular profile; every A4 context has
raw multiplicities

```text
(1/12,1/12,1/12,3/12),                                (ATP3)
```

the C2 edges have `(1/2,1/2)`, and the C3 edges have
`(1/3,1/3,1/3)`.  On the collision `S3` margin the raw profile is

```text
(z_triv,z_sign,z_std)=(1/6,1/6,2/6),                  (ATP4)
```

and the `+1/-1` spectral ranks of `c` are `(1/2,1/2)`.

All A4 incidence equations in `(ATP1)` hold because restriction of a regular
representation is the index multiple of the subgroup regular
representation.  Collision 19243 is exactly zero at `(ATP4)`: the
six-dimensional family `pi_theta` from
`atlas-19243-has-continuous-regular-s3-line-holonomy` restricts to
`Reg(S3)` and has balanced `c`.  Taking `3360` copies gives dimension
`20160`, exactly the restriction scale of `Reg(A8)`, and arbitrary external
amplification preserves the point.

Hence the desired zero-defect locus intersects the exact finite-subgroup
type-profile relaxation at its canonical regular point.  No rational LP
functional of A8/A4/C2/C3/S3 irreducible multiplicities, collision-involution
ranks, or their restriction flows can separate that point.

This is not a full matrix countermodel to the joint atlas packet.  The type
fiber product forgets the common relative unitary and the four rectangle
holonomies.  The theorem instead decides the branch isolated by
`atlas-fixed-packet-arithmetic-has-no-hs-gap`: there is no real
representation-type incompatibility to amplify.  Any remaining obstruction
must prove that the displayed compatible marginals have no common holonomy
lift, or that every such lift pays positive collision/rectangle energy.
