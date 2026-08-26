---
rg: 2
id: small-rotation-canonical-edge-leakage-proof
kind: route
title: Rotate every diagonal coordinate pair by a vanishing angle
target: canonical-moments-admit-divergent-edge-leakage
requires: []
---

Put `A_r=C_2^r`, `d_r=|A_r|=2^r`, and let

```text
D_r(a)=diag_(chi in dual(A_r)) chi(a)                   (CER1)
```

be the Fourier-diagonal form of the regular representation.  The matrices
`D_r(a)`, `a in A_r`, are an orthogonal unitary basis of the diagonal
algebra `mathcal D_(d_r)`.

Pair the `d_r` coordinate vectors arbitrarily.  On every pair put the real
rotation

```text
R(theta_r)=[[cos(theta_r),-sin(theta_r)],
            [sin(theta_r), cos(theta_r)]],
theta_r=d_r^(-1/4),                                     (CER2)
```

and let `U_r` be their direct sum.  Also choose `N_r->infinity` and let
`S_r` be the cyclic shift on `C^(N_r)`.  If `p_r:A->A_r` is truncation to
the first `r` coordinates, define

```text
phi_r(a,k)=D_r(p_r(a)) U_r^k tensor S_r^k.               (CER3)
```

These are unitaries and `phi_r(0,0)=1`.  For fixed `(a,k),(b,l)`, the only
multiplicative error is moving `D_r(p_r(b))` past `U_r^k`.  Since

```text
||U_r-I||_op<=theta_r,
||[U_r^k,D_r(p_r(b))]||_2<=2|k|theta_r,                 (CER4)
```

the maps are pointwise asymptotically multiplicative.

They have canonical limiting character.  If `k!=0`, then for large `r`

```text
tr(S_r^k)=0.
```

If `k=0` and `a!=0`, then eventually `p_r(a)!=0`, and Fourier orthogonality
gives `tr(D_r(p_r(a)))=0`.  This proves the character assertion.

The edge algebra is

```text
B_r=mathcal D_(d_r) tensor 1,
```

and conjugation by `phi_r(0,1)=U_r tensor S_r` restricts to `Ad(U_r)` on
it.  For a diagonal contraction `b`, `(CER4)` with `k=1` gives the pointwise
covariance bound in `(CEL4)`.

It remains to compute the aggregate leakage.  On one coordinate pair,
conjugating `E_11` by `R(theta)` gives off-diagonal entries
`cos(theta)sin(theta)`.  With normalized matrix trace, the two normalized
diagonal basis vectors on that pair contribute together

```text
4 cos^2(theta)sin^2(theta)=sin^2(2theta)                 (CER5)
```

to the squared Hilbert--Schmidt norm of
`(1-E_(B_r))Ad(U_r)E_(B_r)`.  There are `d_r/2` pairs, hence

```text
L_r=(d_r/2)sin^2(2theta_r)
    asymptotic to 2 sqrt(d_r)->infinity.                 (CER6)
```

Tensoring with `S_r` changes neither the normalized edge basis nor this
calculation.  Equations `(CER4)--(CER6)` prove all assertions.
