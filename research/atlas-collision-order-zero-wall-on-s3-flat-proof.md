---
rg: 2
id: atlas-collision-order-zero-wall-on-s3-flat-proof
kind: route
title: Use the exact classical collision defect and word Lipschitz bound
target: atlas-collision-order-zero-wall-on-s3-flat
requires:
  - atlas-fourteen-shifted-tangent-spaces-have-an-s3-flat
  - atlas-a4-classical-opaque-star-sharp-constant
---

The reference alignment is one of the thirty exact inner classical packet
alignments.  `atlas-a4-classical-opaque-star-sharp-constant` computes the
collision defect as `sqrt(2)` on every such alignment.  This proves
`(A4-Q0-1)` exactly (the collision value is a nonidentity left-regular group
unitary and hence has canonical trace zero).

Write

```text
C(U)=U^*rho(b_0)U.
```

The collision word has the form

```text
r C s C r^-1 C (sr) C,
```

so it contains exactly four copies of `C`.  For unitaries `U,V`,

```text
||C(U)-C(V)||_2 <= 2||U-V||_2.
```

Telescoping the four-factor word and using unitary invariance therefore gives

```text
||q_19243(U)-q_19243(V)||_2 <= 8||U-V||_2.             (1)
```

For skew-Hermitian `T`, the integral formula for the unitary exponential
gives

```text
||exp(epsilon T)-1||_2 <= |epsilon| ||T||_2.           (2)
```

Apply the reverse triangle inequality to `(A4-Q0-1)`, then `(1)` with
`V=R`, and finally `(2)`.  This proves `(A4-Q0-2)` and `(A4-Q0-3)`.  The
argument does not use which packet tangent space contains `T`; it applies a
fortiori to their exact common `S3` flat.
