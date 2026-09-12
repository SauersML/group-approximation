---
rg: 2
id: atlas-ef-dual-rows-create-the-prefix-depth-tower
kind: claim
title: The Atlas E/F rows create the dual-prefix Heisenberg depth tower
distinct_from:
  atlas-ef-target-rows-shrink-but-do-not-remove-degenerate-face: that computes the first e/f target translations and leaves a fixed 15/4096 target face; this follows the dual E/F translations and their e/f returns through arbitrary prefix depth.
  leavitt-prefixes-form-exponential-heisenberg-packet: that proves the abstract depth-n prefix packet and its spin-dimension divisibility; this identifies it as the exact continuation of the residual Atlas moving-coefficient face and computes the depth-one residual mass.
  finite-positive-root-fragments-have-marked-regular-models: that gives an exact finite regular model for every bounded positive-root fragment; this shows the E/F continuation is unbounded depth and explains why every fixed truncation still survives.
---

**ESTABLISHED EXACT DEPTH-TOWER REDUCTION.**  Continue from the fixed
`e/f` target face of
`atlas-ef-target-rows-shrink-but-do-not-remove-degenerate-face`.  For
distinct target positions `r,s`, the dual moving roots

```text
x_rs(E),       x_rs(F)                                (EFT1)
```

act on the `p=eE`, `q=fF` target characters through the four new
coefficients

```text
pE=eEE,       qE=fFE,       pF=eEF,       qF=fFF.     (EFT2)
```

These four normal-form monomials are linearly independent.  On one target
character sector, if their sign bits are `alpha,beta,gamma,delta`, the two
dual actors have the affine action

```text
x_rs(E): (u,w) |->
             (u+alpha e_r, w+(alpha+beta)e_r),
x_rs(F): (u,w) |->
             (u+gamma e_r, w+(gamma+delta)e_r).       (EFT3)
```

Thus active `E/F` signs can again move a degenerate type into the balanced
region.  But at the three target positions there is an exact depth-one fixed
face on which all twelve signs in `(EFT2)` are positive.  They are independent
of the previous six `e/f` signs and of the six `p/q` signs.  Its intersection
with the earlier survivor therefore has canonical target trace

```text
(15/4096) 2^(-12) = 15/2^24,                          (EFT4)
```

and marked ambient trace `15/2^25`.  So `E/F` alone still does not eliminate
the face.

The return/incidence rows change the nature of the survivor.  Write

```text
s_0=e, s_1=f,       t_0=E, t_1=F.
```

The literal CK relations are

```text
t_i s_j=delta_(i,j),       s_0t_0+s_1t_1=1.           (EFT5)
```

For binary words `alpha,beta` of length `n`, the derived rows give

```text
t_alpha s_beta=delta_(alpha,beta).                    (EFT6)
```

Consequently the positive roots

```text
X_alpha=x_13(t_alpha),
Y_beta =x_32(s_beta),
J      =x_12(1)                                         (EFT7)
```

form `2^n` independent Heisenberg pairs with common center:

```text
[X_alpha,Y_beta]=J^(delta_(alpha,beta)).               (EFT8)
```

On the `J=-1` sector, finite Stone--von Neumann theory forces dimension
divisible by

```text
2^(2^n).                                                (EFT9)
```

Thus the common center is the original marked first root, not a new target
sign.  Since `(EFT9)` holds for every `n`, the exact closure of the `E/F`
rows plus their incidence returns has no nonzero finite-dimensional marked
sector.
The finite faces `(EFT4)` do not converge to another finite terminal face;
they are successive levels of the dual-prefix depth tower.

This does **not** give a normalized-HS contradiction.  For every fixed depth
`n`, the packet in `(EFT7)--(EFT8)` is a finite positive-root fragment and
has its marked left-regular matrix model.  A microstate sequence may let the
available spin dimension and authenticated prefix depth tend to infinity
together.  The literal finite presentation controls every fixed `n`
eventually, but the derivation length and required dimension grow with `n`.

Therefore the positive Atlas route has reached a precise remaining model:
an ultra-deep dual-prefix tower carrying the residual orientation
multiplicity.  Closing it requires a depth-free same-reservoir estimate, or
constructing coherent finite-depth regular models whose depth increases with
matrix size.  No additional bounded collection of positive-root return rows
can decide between those alternatives.

DERIVATION
atlas-ef-dual-prefix-tower-proof
