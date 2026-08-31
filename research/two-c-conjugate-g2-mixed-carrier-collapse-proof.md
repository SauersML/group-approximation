---
rg: 2
id: two-c-conjugate-g2-mixed-carrier-collapse-proof
kind: route
title: Compute two independent hidden signs and collect the doubled S leg
target: two-c-conjugate-g2-mixed-carriers-collapse-to-one-orientation
requires:
  - fixed-g2-mixed-pair-has-all-length-d8-normal-form
  - first-g2-mixed-return-has-a-dihedral-half-absorber
---

## 1. The second shifted covector

Use the active basis from `(GMR15)`. The quotient generator `k` acts
on the source module by

```text
r=[[0,1],[1,1]],                 r^(-1)=[[1,1],[1,0]].
```

It fixes the trivial coordinate `c_3`. Therefore conjugating `U_0` by
`k` replaces its covector `phi_0=(1,0)` by

```text
phi_1=phi_0r^(-1)=(1,1).
```

Both covectors take value one on `v=(1,0)^t`, the vector used by the
sign roots `A` and `W`. They are distinct. With
`p=ST=1-q` and `a=qT`, the two returned roots and their commutators
with `A` are

```text
P_i=I+p E_(c_0,phi_i),
Z_i=(P_iA)^2=I+aE_(v,phi_i).                            (TCC5)
```

The calculation is the same two-by-two rectangular multiplication as
`(GMR10)`: `pa=0` and `ap=a`. Since `a^2=0`,

```text
Z_0Z_1=I+aE_(v,phi_0+phi_1) !=I,
[Z_0,Z_1]=1.                                            (TCC6)
```

Thus the two signs are independent. They commute with `H,A,W` and with
both `U_i,V`; the potentially nonzero coefficient in the latter check is
`Ta=0`.

For every `i`, the matched branch identity gives `VAV=AW`, while the
opposite rectangular corner gives `U_iWU_i=WZ_i`. The other two
cross-conjugations are trivial. Since `Y_i^(-1)=U_iV`, this proves
`(TCC3)`.

## 2. Exhaust the four two-carrier polar squares

Let `M_i` denote conjugation by `Y_i^(-1)` on the abelian sign group.
Writing multiplication additively over `F_2`,

```text
M_i:       A |-> A+W+Z_i,          W |-> W+Z_i,
M_i^(-1): A |-> A+W,              W |-> W+Z_i.          (TCC7)
```

The `Z_j` are fixed. Exact composition gives

```text
M_1 M_0:
 A |-> A+Z_0,              W |-> W+Z_0+Z_1,

M_1^(-1) M_0:
 A |-> A+Z_0+Z_1,          W |-> W+Z_0+Z_1.             (TCC8)
```

The other two exponent choices give the same two systems with the
indices reversed. Intersecting the conjugated sign projection with the
outer `A=sigma,W=tau` carrier shows:

- in the equal-orientation case, `Z_0=Z_1=+1`;
- in the opposite-orientation case, `Z_0Z_1=+1`.

This proves the two support projections in the claim. Each compressed
carrier is a partial isometry because its initial square is a projection.

## 3. Exact rank certificates

The finite active group from `(GMR15)` already contains `P_1`:
it is the `k`-conjugate of `P_0`. Thus it still has order `6144`.
For the equal-orientation projection use

```text
B_2=<H,A,W,Z_0,Z_1> isomorphic to C_2^5.
```

There are `6144/32=192` rows indexed by `B_2`-character cosets and
`6144/3=2048` columns indexed by `<k>`-character cosets. As in the
one-sign certificate, each column has at most three entries with
coefficients `1,omega^2,omega`. Exact elimination over
`Q[omega]/(omega^2+omega+1)` gives

| `(sigma,tau)` | rows | columns | pivots |
|---|---:|---:|---:|
| `(+,+)` | 192 | 2048 | 184 |
| `(+,-)` | 192 | 2048 | 180 |
| `(-,+)` | 192 | 2048 | 180 |
| `(-,-)` | 192 | 2048 | 180 |

The elimination uses the canonical eight-element coefficient triples
from `(GMR9)`; pivot rows have support at most seven and all exact
numerators and denominators have at most three binary digits.

For the opposite-orientation projection replace the last two generators
by `Z_0Z_1`. The Fourier subgroup again has order sixteen, and the exact
pivot counts are `344` for `(+,+)` and `336` for the other three
signs, exactly the one-hidden-sign table.

The source `R` selects two central `h` characters. Doubling and dividing
by `3*6144=18432` gives

```text
2*184/18432=23/1152,          2*180/18432=5/256,

2*344/18432=43/1152,          2*336/18432=7/192.        (TCC9)
```

All are below `1/18`. A left target cut or a left power of `g_2`
cannot increase an initial support rank.

## 4. Why sign cancellation also cancels S

The two negative roots commute, so

```text
U_Delta=U_0U_1=I+T E_(c_3,phi_0+phi_1).
```

Their commutators with the common positive root also multiply:

```text
P_Delta=[V,U_Delta]=P_0P_1.
```

Using `VU_iV=P_iU_i` gives

```text
Y_0Y_1=VU_0VU_1=P_0U_Delta,

Y_0Y_1^(-1)=VU_0U_1V=P_Delta U_Delta.                  (TCC10)
```

Inverses and reversed products have the same collected coefficient set.
Only `p=1-q` and `T` remain. Therefore all four words lie in the
negative one-letter algebra `B_-`, and adjoining scalar routers keeps
them in the established residually finite matrix group.

This explains the polar table algebraically. The only two-carrier
recombination which can merge `Z_0` and `Z_1` also pairs the common
`V` occurrence with itself. Its positive raw letter disappears before
the target leg is applied.
