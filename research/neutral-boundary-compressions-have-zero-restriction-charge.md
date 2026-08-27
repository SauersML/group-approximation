---
rg: 2
id: neutral-boundary-compressions-have-zero-restriction-charge
kind: claim
title: Every neutral endpoint compression has zero native restriction-lattice charge
distinct_from:
  three-way-cell-semigroups-have-conductor-but-unbounded-charge: that constructs wrong-lattice fractional tables for abstract moving supports; this proves such a charge cannot occur in a compression of an exact endpoint by an extendible neutral boundary.
  positive-fixed-corner-cubic-energy-charges-deleted-rank: that charges the boundary rank analytically after an exact dilation is supplied; this identifies the corresponding representation-semigroup class and combines the two conclusions.
  bs14-residual-polar-data-build-active-dilation: that starts with an arbitrary near tuple and must manufacture a dilation; this proves the lattice and padding statements only once such a dilation exists.
---

Let `Gamma` be a group, let `B<=Gamma`, and let

```text
res: Rep_+(Gamma) -> Rep_+(B),
L_B=gp(res(Rep_+(Gamma))).                              (NRC1)
```

Suppose an exact finite-dimensional representation `pi` of `Gamma` has a
`B`-invariant orthogonal decomposition

```text
H=QH (+) PH,
pi|_(QH)=tau^r,                                       (NRC2)
```

where the `B`-representation `tau` extends to a representation of `Gamma`.
If `beta=pi|_(PH)` is the compressed core type, then

```text
[beta]=res[pi]-r[tau] in L_B.                         (NRC3)
```

Thus every such compressed core has zero class in the quotient of the
ambient `B`-representation group by the endpoint restriction lattice.

For the neutral BS14/Iwahori boundary, `tau` is the trivial representation.
Consequently every positive-corner compression of an exact Iwahori endpoint
automatically lies in the correct native restriction lattice, regardless of
how the endpoint couples distinct scalar BS packets.  If, in addition, the
positive boundary compression satisfies the spectral hypothesis of
`positive-fixed-corner-cubic-energy-charges-deleted-rank`, then the same
boundary is an explicit support-changing repair with

```text
padding rank r <= cubic Frobenius energy/f(a_0),       (NRC4)
```

and generator displacement `O(sqrt(r/d))` after normalization.

Hence neither semigroup nonnormality nor a hidden lattice charge obstructs
the arbitrary cross-packet problem **inside an authenticated exact
dilation**.  The only remaining place a wrong-lattice charge could occur is
an approximate torsion frame which does not come from such a compression.
Excluding that case is exactly the reverse boundary-dilation/authentication
theorem; small normalized-HS residuals alone cannot supply it through a
determinant, since determinant charge is HS-discontinuous.
