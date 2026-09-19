---
rg: 2
id: steinberg-fox-chord-action-proof
kind: route
title: Multiply the seven coefficient matrices on normalized point-plane flags
target: steinberg-fox-chord-actions-are-explicit
requires:
  - steinberg-cycles-have-big-cell-chord-coordinates
---

Represent `(SBC2)` by the column and row

```text
v=(1,a,b)^T,                    phi=(ac-b,-c,1).        (SCAP1)
```

For a coefficient `g`, the flag `g^(-1)C(a,b,c)` is represented by

```text
(g^(-1)v,phi g).                                      (SCAP2)
```

It is a chord exactly when the first coordinate of `g^(-1)v` and the third
coordinate of `phi g` are both nonzero.  Normalizing those two coordinates
then gives `(SCA1)`.

For the lower roots, left multiplication of

```text
L(a,b,c)=((1,0,0),(a,1,0),(b,c,1))                    (SCAP3)
```

gives directly

```text
x_21(1/2)L(a,b,c)=L(a+1/2,b,c),
x_32(1/2)L(a,b,c)=L(a,b+a/2,c+1/2),                   (SCAP4)
```

which proves the formulas for `q=x_21(-1/2)` and `s=x_32(-1/2)`.

For the remaining coefficients use

```text
A=I+2E_12,
B=diag(2,1/2,1)(I+2E_23),
u=I+E_13-(1/2)E_23,
r=I-E_23,
h=diag(2,1,1/2).                                     (SCAP5)
```

Substitution in `(SCAP2)` gives respectively

```text
A:  g^(-1)v=(1-2a,a,b),
    phi g=(ac-b,2(ac-b)-c,1);

B:  g^(-1)v=(1/2,2a-2b,b),
    phi g=(2(ac-b),-c/2,1-c);

u:  g^(-1)v=(1-b,a+b/2,b),
    phi g=(ac-b,-c,1+ac-b+c/2);

r:  g^(-1)v=(1,a+b,b),
    phi g=(ac-b,-c,1+c).                              (SCAP6)
```

After normalizing the first column coordinate and the last row coordinate,
the incidence identity forces precisely the four rational formulas in
`(SCA2)`.  For `g=h^(-1)`, `(SCAP2)` uses `h`; conjugation of `(SCAP3)` by
`h` sends `(a,b,c)` to `(a/2,b/4,c/2)`.  This proves all seven formulas.

When a normalizing coordinate in `(SCAP6)` is zero, the transformed point
lies in `H_0` or the transformed plane contains `z`.  By `(SBC1)` its flag is
in `T`, and `(SBC3)` supplies its coefficient.  Conversely those are exactly
the two conditions for membership in `T`, so there are no omitted strata.

Finally `E_pR_p` is the identity on `St_p`, which is invariant under every
group element.  Therefore

```text
L_gL_h=R_pgE_pR_phE_p=R_pghE_p=L_(gh),                (SCAP7)
```

proving `(SCA3)`.
