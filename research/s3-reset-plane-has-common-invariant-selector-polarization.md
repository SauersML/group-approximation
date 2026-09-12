---
rg: 2
id: s3-reset-plane-has-common-invariant-selector-polarization
kind: claim
title: A compatible reset plane has one S3-invariant old-to-fresh selector polarization
distinct_from:
  affine-selector-clifford-rank-swap-balanced: that chooses a Witt frame for one reset direction; this gives one frame and one Clifford transform compatible with all three nonzero directions of a reset plane.
  s3-equivariant-affine-clifford-return-edge: that must also include the residual derivative packet and the next BCS endpoint semantics; this closes only the selector symplectic geometry.
---

Let `A` be a two-dimensional subspace of the four semantic selector
coordinates and choose a complementary plane `C`.  Let
`H=GL(A)=S_3` act naturally on the `X_A` Paulis, contragrediently on the
`Z_A` Paulis, and trivially on the `C` coordinates and the dummy qubit.
In the semantic selector symplectic space, put

```text
L_old = Z_A direct_sum Z_C,
L_new = X_A direct_sum Z_C.                              (SRP1)
```

Both are `H`-invariant Lagrangians.  Every nonzero reset translation
`T_a=X_a`, `a in A-{0}`, lies in the **same** fresh Lagrangian `L_new`.
Fix the `H`-invariant alternating form on `A`, represented in a symplectic
basis by

```text
Omega=[[0,1],[1,0]].                                    (SRP2)
```

The selector symplectic transformation

```text
W_A:(x,z) |-> (Omega z, Omega x)                        (SRP3)
```

on `A_X direct_sum A_Z`, extended by the identity on `C` and the dummy
qubit, commutes with `H` and maps `Z_A` onto `X_A`.  It is implemented by one
finite selector Clifford word.  Consequently

```text
W_A L_old W_A^(-1)=L_new                                (SRP4)
```

equivariantly for the entire three-direction orbit.  Fixing a full character
of either Lagrangian cuts the four semantic qubits to dimension one and
leaves the dummy qubit free, so both sides retain the same two-dimensional
dummy spin before tensoring with the rank-fifteen residual.

This removes direction-dependent Witt choices from the proposed `S_3`
return.  It does not by itself say that all residual derivative words extend
over the fresh generators.  That finite compatibility and its zero-kernel
regular stabilization are now checked in
`regular-clifford-edge-map-has-zero-kernel`; the remaining return problem is
the global endpoint semantics, not selector symplectic geometry.
