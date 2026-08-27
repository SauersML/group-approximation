---
rg: 2
id: affine-sign-twist-swaps-active-blocks-but-is-stationary
kind: claim
title: The affine sign swaps the two active M3 blocks but its Toeplitz return is period-two stationary
distinct_from:
  packet-headed-toeplitz-shift-is-schur-type-preserving: that proves the untwisted shift preserves every full packet block; this allows the only new affine sign symmetry and computes that it merely permutes the two active blocks.
  toeplitz-s3-headed-holonomy-compressor: that absorbs an external S3 sign character in a finite head; this computes the internal affine active Wedderburn blocks on which that sign acts.
  reset-ray-hnn-return-is-stationary: that finds the scalar stationary ray after a finite Schur reset; this is the exact two-cycle in the affine coefficient algebra.
---

Let `e_+` and `e_-` be the two primitive central idempotents of the active
corner

```text
A k[C_aff] ~= M_3(k)e_+ direct_sum M_3(k)e_-.             (AST1)
```

Let `chi:C_aff->C_2` be the sign of the quotient `S_3`, and let

```text
Theta_chi(sum_g a_g g)=sum_g a_g chi(g)g.                 (AST2)
```

Then

```text
Theta_chi(e_+)=e_-,        Theta_chi(e_-)=e_+,            (AST3)
Theta_chi(A)=A.                                               
```

Indeed the active `D`-character orbit has stabilizer `C_2`.  The two active
irreducibles are induced from the trivial and sign characters of this
stabilizer, and tensoring with the ambient `S_3` sign exchanges them.

The sign-twisted Toeplitz endomorphism

```text
sigma_chi(a)=x Theta_chi(a)y+epsilon(a)A                  (AST4)
```

is proper, injective, and unital.  On the two active blocks it satisfies

```text
sigma_chi(e_+)=x e_- y,
sigma_chi(e_-)=x e_+ y,
sigma_chi^n(A)=x^n A y^n.                                (AST5)
```

Thus the affine sign supplies a genuine non-type-preserving operation, but
its transition matrix on active block multiplicities is

```text
[[0,1],[1,0]],                                             (AST6)
```

whose spectral radius is one.  The total active current is fixed and the
transverse current only changes sign.  No iteration of this twist yields the
strict coefficient `lambda<1` required by `(HST2)`.

Consequently the internal sign swap is useful as a chart equalizer or parity
label, but it cannot by itself replace a branching child-MASA/proper-corner
map.  A successful return must send one source block into more than one
target channel, or charge the transverse current to relator energy; a
periodic permutation of simple blocks is stationary.
