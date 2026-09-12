---
rg: 2
id: odd-root-branch-firewall-proof
kind: route
title: Rotate nearly antipodal root pairs in a finite regular congruence packet
target: relative-first-triangle-rounding-has-an-odd-root-branch-firewall
requires:
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
---

Fix an odd prime `p`, let `G=PSL_2(F_p)`, and use its left regular
representation.  The standard unipotent `S` has order `p`; its eigenspaces

```text
E_j=ker(S-omega^j),       omega=exp(2 pi i/p),
```

all have the same dimension `|G|/p`.  Together with the diagonal element
`R` and Weyl involution `X_0`, these operators form an exact finite Iwahori
tuple.  Put `A_0=X_0S^2`, so `A_0^3=1`.

Write `n=(p-1)/2`.  Pair `E_j` with `E_(j+n)` for `0<=j<n`, leave
`E_(p-1)` fixed, and let `U` be the Hadamard rotation on each paired
multiplicity space.  Define

```text
X_p=UX_0U^*,          A_p=UA_0U^*,
Q_p=X_pA_p=US^2U^*.                                  (FRP1)
```

The first two exact relations in `(FTR1)` follow immediately.  On a paired
block the two eigenvalues of `S^2` differ by

```text
|omega^(2j)-omega^(2j+2n)|=|1-omega^(-1)|<=2 pi/p.
```

Conjugating a two-by-two diagonal matrix by the Hadamard changes it in
normalized HS norm by its eigenvalue gap divided by `sqrt(2)`.  Summing the
orthogonal equal-multiplicity blocks proves `(FTR2)`, and

```text
||X_pS^2-A_p||_2=||S^2-Q_p||_2.
```

Telescoping the cube against `A_p^3=1` proves `(FTR4)`.

It remains to prove the constant root gap.  Since the eigenvalues of `S^2`
are distinct, the spectral blocks of `Q_p` are exactly the rotated spaces
`UE_j`.  Every square root `T` of `Q_p` commutes with `Q_p`, because
`TQ_p=T^3=Q_pT`.  Hence

```text
dist_2(S,{Q_p}') <= ||S-T||_2.                         (FRP2)
```

In the `Q_p` spectral basis, the off-diagonal part of `S` on the pair
`E_j (+) E_(j+n)` has coefficient

```text
(omega^j-omega^(j+n))/2,
```

so its squared normalized distance from the block-diagonal algebra is
`|1-omega^n|^2/4=cos^2(pi/(2p))`.  The paired blocks occupy fraction
`(p-1)/p` of the whole regular representation.  Conditional expectation
onto `{Q_p}'` and `(FRP2)` therefore give `(FTR3)`.

The lower bound concerns every root of `Q_p`, independently of how its
return monodromy is represented.  Re-exactifying `R` cannot help because
the obstruction is present before `R` is chosen.

