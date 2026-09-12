---
rg: 2
id: binary-jacobson-finitary-kernel-proof
kind: route
title: Identify the defect ideal with finitary matrices and use the infinite simple kernel
target: binary-jacobson-elementary-mark-is-finite-quotient-invisible
requires:
  - leavitt-first-offdiagonal-packet-has-jacobson-orbit-quotient
---

On the standard basis of `V=direct_sum_(n>=0) F_2 e_n`, put

```text
E_mn=S^m Q T^n,                 Q=1-ST.
```

These are the ordinary matrix units, and their span `F` is the ideal of all
finite-support matrices.  Modulo `F`, the classes of `S,T` are inverse, so

```text
J/F ~= F_2[z,z^(-1)].                                  (JFQ2)
```

Passing to five-by-five elementary groups gives a surjection onto
`EL_5(F_2[z,z^(-1)])`.  Its kernel consists of the invertible operators on
`V^5` which differ from the identity in a finite matrix.  Over `F_2` this is
the finitary special linear group

```text
L=GL_fin(N x {1,...,5},F_2)=SL_fin(N x {1,...,5},F_2).
```

To see that the whole group occurs, elementary roots with coefficients
`E_mn` give transvections between basis vectors of two different coordinate
rays.  Commutators through a third coordinate give the transvections within
one ray.  These generate every finite-dimensional `SL`, and their union is
`L`.  Conversely an element with trivial symbol differs from the identity by
a finite matrix and lies in that union.  The ideal property, or direct
conjugation on finite matrices, makes `L` normal in `E`.

The group `L` is infinite simple.  A quick standard proof is to place a
nonidentity element of a normal subgroup in a sufficiently large finite
special linear group, commute it with an elementary transvection using one
fresh basis vector, and obtain a nonidentity transvection.  All elementary
transvections are conjugate in the infinite group and generate `L`.

Now let `phi:E->F_0` with `F_0` finite.  The kernel of `phi|L` is normal in
the infinite simple group `L`.  An injective restriction is impossible, so
`phi` kills `L`.  Since

```text
z_Q=x_13(E_00) in L\{1},
```

every finite quotient kills the marked root.

Finally, in a finite-dimensional unital ring image, `TS=1` says that the
linear map `S` has a left inverse.  It is therefore bijective, with inverse
`T`, and `ST=1`.  Thus the defect `Q=1-ST` is zero in every such ring image,
which proves the stated finite-truncation fence.
