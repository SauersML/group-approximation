---
rg: 2
id: iwahori-torsion-normalization-proof
kind: route
title: Round the two cubic products and redefine their shared coordinates
target: iwahori-two-triangle-torsion-normal-form
requires:
  - iwahori-square-free-bs14-presentation
---

For a unitary `V`, nearest-root functional calculus gives an order-three
unitary `V_0` with

```text
||V-V_0||_2<=(1/2)||V^3-1||_2.                        (TNP1)
```

Indeed, if `Delta in [-pi/3,pi/3]` is the angular distance to the nearest
cube root, then

```text
2sin(|Delta|/2)<=sin(3|Delta|/2)
```

and integration over the spectrum proves `(TNP1)`.

Apply this first to `A=XT`.  Choose `A_0^3=1` with
`||A-A_0||_2<=eta/2` and define

```text
T_1=XA_0.
```

Since `X^2=1`, `XT_1=A_0`, proving the first equation in `(TTN1)` and the
first bound in `(TTN2)`.  Put `B_1=XT_1^2R`.  Fixed-word telescoping gives

```text
||B_1^3-1||_2<=zeta+3eta.                             (TNP2)
```

Round `B_1` to `B_0^3=1` with

```text
||B_1-B_0||_2<=(zeta+3eta)/2
```

and define

```text
R_1=T_1^(-2)XB_0.                                    (TNP3)
```

Then `XT_1^2R_1=B_0`, proving the second equation in `(TTN1)`.  Since the
same expression with `B_1` in place of `B_0` equals `R`, `(TNP3)` also gives
the second bound in `(TTN2)`.

Changing the two occurrences of `R` in the inversion row costs at most
twice `||R_1-R||_2`, which proves `(TTN3)`.  Before the `R` change, replacing
`T` by `T_1` changes BS covariance by at most

```text
||T_1-T||_2+||T_1^4-T^4||_2<=5eta/2.
```

Changing the two occurrences of `R` then costs at most
`2||R_1-R||_2<=zeta+3eta`.  This proves `(TTN4)`.

Finally, nearest-sign spectral rounding of an approximately involutive
unitary gives

```text
||X-X_0||_2<=||X^2-1||_2.                             (TNP4)
```

For a scalar whose angular distance from the nearer sign is
`Delta in [0,pi/2]`, this is `2sin(Delta/2)<=2sin(Delta)`.  Perturbing `X`
first and telescoping the four fixed words proves the stated general
vanishing-defect corollary.
