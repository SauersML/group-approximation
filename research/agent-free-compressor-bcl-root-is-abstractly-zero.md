---
rg: 2
id: agent-free-compressor-bcl-root-is-abstractly-zero
kind: claim
title: The fully identified BCL root is already abstractly trivial
distinct_from:
  agent-free-compressor-full-corner-root-is-fd-invisible: That proves finite-dimensional invisibility by passing to a finite common-root coefficient quotient; this proves the stronger coefficient-ring identity before taking any representation.
  agent-free-compressor-padded-j-row-kills-payload-root: That uses one specially padded quotient row to give a two-line bounded derivation; this uses the original complete parent and child packet algebras and needs no padding.
  schur-toeplitz-root-mark-is-fd-invisible: That packet defect is nonzero in its coefficient ring and is killed only by finite directly-finite quotients; the BCL corner idempotent here is zero in the coefficient ring itself.
---

Let `P` be one primitive forbidden packet block in the coefficient ring with
the complete rows `(BCL0)--(BCL2)`.  On this block the Schur--Clifford packet
algebras have the strict inclusion

```text
P k[B_f]=M_(2D)(k),
P k[A_f]=M_D(k) tensor k I_2.                          (BAZ1)
```

Then

```text
P=0                                                     (BAZ2)
```

in the presented coefficient ring.  Consequently every Steinberg
wordization satisfies

```text
x_ij(P)=1                                               (BAZ3)
```

in the abstract group, not merely in its finite-dimensional
representations.  The same conclusion holds for a sum of forbidden primitive
blocks, block by block.

Hence the root in `agent-free-compressor-full-corner-root-is-fd-invisible`
does not have an injected order-`p` cyclic subgroup and cannot be used as the
edge of a literal `C_p` amalgam.  Its proposed asymptotic collapse `(FCI3)` is
automatic by fixed-relator telescoping and is not the missing
normalized-HS theorem.  The missing operation remains a physical
packet/BCS-to-root coupling with a **different abstractly nontrivial root**,
or a conditional construction which does not first impose all three BCL
rows in one coefficient-ring quotient.

There is no perfect-completeness contradiction.  The intended perfect
tracial BCS model already has every forbidden `P` equal to zero, so `(BAZ2)`
does not kill the marked central sign.  It only shows that this particular
root cannot carry the forbidden mass in the abstract group.

