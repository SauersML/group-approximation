---
rg: 2
id: steinberg-fox-kernel-is-flag-incidence
kind: claim
title: The two Fox rows on the defining-characteristic SL3 Steinberg module are one explicit flag-incidence kernel
artifacts:
  - research/steinberg-flag-incidence-reduction-proof.md
distinct_from:
  symmetric-power-fox-kernel-is-smith-obstruction: that is a Smith-normal-form reduction for pure symmetric powers over Z[1/2]; this is the separate mixed-highest-weight Steinberg block in defining characteristic.
---

Let `p` be odd, `k=F_p`, `G=SL_3(k)`, `B` the upper triangular Borel,
and `P_1,P_2` the two standard maximal parabolics containing `B`.  Put

```text
C_1=k[G/B],                 C_0=k[G/P_1] directSum k[G/P_2],
partial(gB)=(-gP_1,gP_2).                                (SFI1)
```

For the two universal group-ring rows

```text
X=A-Aq+B-Bs-1,
Y=1-q-u+uq-h^(-1)r+h^(-1),                              (SFI2)
```

define

```text
D_p:C_1 -> C_0 directSum C_1 directSum C_1,
D_p(f)=(partial f,Xf,Yf).                               (SFI3)
```

Then the common affine-translation kernel of `X,Y` on the Steinberg module
is canonically

```text
ker(X|St_p) intersect ker(Y|St_p)=ker D_p.              (SFI4)
```

Equivalently, the Steinberg block is safe exactly when the single explicit
flag-incidence map `D_p` is injective.  In point--plane coordinates a flag
is a pair `([v],[phi])` with `phi(v)=0`; `partial f=0` says that the sum of
the coefficients of `f` over every point panel and every plane panel is
zero, while `(SFI2)` gives two fixed finite-difference equations under the
ten displayed projective transformations.

This reduction is uniform in `p`, but it is not a six-dimensional Weyl-sign
test.  The standard-apartment span is not preserved even by the individual
coefficient `A=x_12(2)`: on the chamber `s_1B`, conjugation turns `A` into a
nontrivial lower-root element, and `A s_1B` is not a Weyl-representative
chamber.  Thus root-group parameters, not only Weyl signs, are essential.
The other canonical one-dimensional candidate also fails immediately: if
`v` is fixed by the lower unipotent `U^-`, then `qv=sv=v` and `(SFI2)` gives
`Xv=-v`, so the `U^-`-fixed Steinberg line contains no common-kernel vector.
At the opposite extreme, the `B`-fixed highest-weight line lies in `ker Y`
but not in `ker X`: the two nontrivial terms of `Xv` are nonzero multiples
of the distinct PBW vectors `f_1^(p-1)v` and `f_2^(p-1)v`.  Thus neither
canonical extremal line is the sought obstruction.

DERIVATION
steinberg-flag-incidence-reduction-proof
