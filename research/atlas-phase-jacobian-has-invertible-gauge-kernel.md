---
rg: 2
id: atlas-phase-jacobian-has-invertible-gauge-kernel
kind: claim
title: The Atlas phase-cycle Jacobian has an invertible scalar-gauge kernel
distinct_from:
  atlas-phase-cycle-determinant-is-gauge-trivial: that shows scalar gauge erases determinant and index data; this shows the same symmetry inserts an invertible matrix into every Jacobian-kernel operator space and forbids shrinkage.
  spectral-low-energy-shrunk-space-obstruction: that converts a shrunk low-energy operator space into an energy floor; this rules out the most direct Jacobian construction of such a space for the Atlas phase cycles.
  atlas-spectral-shrunk-intertwiner-certificate: that permits an arbitrary mixed low-energy quadratic form; this excludes only forms obtained from the differential of the scalar-gauge-invariant phase holonomies.
---

**ESTABLISHED FIREWALL.**  Let

```text
F(U)=(H_0(U),H_11(U),H_30(U),H_44(U),H_55(U),H_int(U))
```

be the six multiplicative holonomies in the twenty-seven-phase reduction,
before subtracting their identity targets.  At every relative chart unitary
`U`, the real differential satisfies

```text
dF_U(iU)=0.                                            (PJK1)
```

Indeed the entire curve `t -> exp(it)U` has constant image under `F`.
The tangent vector `iU` is itself invertible.

Let `K_U <= M_d(C)` be any complex operator space which contains the
scalar-gauge tangent kernel--in particular, the complex span of `ker dF_U`,
or the complexified zero-energy space of the Gauss--Newton form
`dF_U^*dF_U`.  Then `K_U` contains `iU`, and hence for every subspace
`X <= C^d`,

```text
dim K_U(X) >= dim (iU)X=dim X.                         (PJK2)
```

Thus `K_U` has no nonzero shrunk subspace.  This remains true at points where
the six holonomies have nonzero defect: scalar gauge fixes their values, not
merely their common zero set.

Consequently one cannot prove
`atlas-spectral-shrunk-intertwiner-certificate` by taking the Jacobian of the
five boundary cycles plus the interior cycle and feeding its nullspace to
operator scaling.  The gauge direction supplies an exact invertible member
at every matrix size.  A viable singular-subspace certificate must first
quotient or pin the scalar gauge in a way that preserves a complex operator
space and the actual relative unitary, or it must use a different mixed
quadratic form whose low-energy space does not automatically contain that
invertible direction.
