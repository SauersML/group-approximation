---
rg: 2
id: kt-return-compressor-gauges-separate
kind: claim
title: Return form and compressor correspondence have separate exact finite gauges
distinct_from:
  kt-extrinsic-corrector-is-an-orthogonal-index-one-correspondence: That identifies the exact correspondence required of one successful seam corrector; this constructs finite canonical actor blocks with separate return-form and compressor-covariant cyclic vectors having identical module data.
  finite-quotient-blindness: That proves the compressed subgroup and its parent have the same finite image; this uses that equality to build an orthogonal index-one correspondence implementing the resulting compressor automorphism.
  kazhdan-and-transverse-packets-cannot-orient-clifford-twist: That allows an arbitrary spectator sign on a generic exact packet model; this identifies the two distinct spectator gauges relevant to the Kun--Thom return and compressor left action.
---

Let `Gamma<G` be the Kun--Thom pair, let
`t Gamma t^(-1)<Gamma` be a strict compressor, and fix a nontrivial root
involution `a in Gamma`.  There are exact finite-image representations

```text
rho_n:G->U(d_n)
```

with canonical limiting character and edge algebras

```text
B_n=C*(rho_n(Gamma))
```

which contain two orthogonal unitary cyclic vectors `u_n,z_n` with the
following properties.

1. **Return-form gauge.**  There is a unitary `S_n` such that

   ```text
   u_n=S_n^*rho_n(a)S_n,       E_(B_n)(u_n)=0,          (SCG1)
   ```

   and `u_n` commutes with `B_n`.

2. **Compressor-correspondence gauge.**  If

   ```text
   theta_n=Ad(rho_n(t))|_(B_n),
   ```

   then

   ```text
   z_n b=theta_n(b)z_n          for every b in B_n,
   E_(B_n)(z_n)=0.                                      (SCG2)
   ```

Both generated correspondences are orthogonal index-one `B_n`--`B_n`
correspondences with full left and right support:

```text
closure(B_n u_n B_n)=u_nB_n,
closure(B_n z_n B_n)=z_nB_n,                            (SCG3)
```

and both left and right Murray--von Neumann dimensions equal one.  Their
normalized ranks inside `L2(M_(d_n))` tend to zero.

Thus even after adding an exact left action implementing the finite-image
compressor, canonical subgroup character and complete left/right
correspondence data do not authenticate the returned cyclic vector.  Finite
quotient blindness supplies two independent gauges:

```text
u_n : exact returned root occurrence with identity left action,
z_n : exact compressor left action with an external spectator sign.       (SCG4)
```

This is not a countermodel to the full relative microstate problem because
the **same** vector is not asserted to satisfy both lines of `(SCG4)`.  It
proves that this same-vector occurrence is precisely the new information a
full strict-actor argument must extract; dimensions, supports, orthogonality,
and the abstract correspondence isomorphism class cannot do so.

DERIVATION
kt-two-correspondence-gauges-proof
