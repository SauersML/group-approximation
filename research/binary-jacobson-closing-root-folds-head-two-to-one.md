---
rg: 2
id: binary-jacobson-closing-root-folds-head-two-to-one
kind: claim
title: The closing Jacobson root folds the two head-Weyl signs onto one raw range
artifacts:
  - research/binary-jacobson-closing-root-fold-proof.md
distinct_from:
  binary-jacobson-naive-head-polar-is-balanced-return: that gives one equal-rank return from the negative Weyl sign; this uses the missing constant active-cycle root to put the positive sign through the same range.
  binary-jacobson-head-weyl-cut-is-native-pi-source: that identifies one sign cut as a degree-two PI source; this combines both signs into an exact coisometry from the entire head sector.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks the fold to intertwine a degree-two source with the literal degree-four target; this authenticates the fold occurrence but does not establish those four intertwining rows.
---

**ESTABLISHED.**  Retain the notation of
`binary-jacobson-naive-head-polar-is-balanced-return`:

```text
P=(1-rho(x_13(Q)))/2,
Y=rho(x_23(Q)),
E_-=P(1-Y)/2,             E_+=P(1+Y)/2,
R=P rho(a_12)P,           R^*R=E_-,      RR^*=F.         (JCF1)
```

Let `b=x_12(1)`, the constant root missing from the first opposite-polar
package.  It preserves `P` and exchanges `E_-` and `E_+`.  Therefore

```text
R_-=R,                    R_+=R rho(b)
```

are partial isometries with orthogonal initial projections `E_-,E_+` and
the identical final projection `F`.  Their cross ranges vanish:

```text
R_- R_+^*=0=R_+ R_-^*.                                  (JCF2)
```

Consequently the finite-coordinate linear combination

```text
T=2^(-1/2)(R_-+R_+)                                     (JCF3)
```

is an exact coisometry from the whole head sector onto the raw range:

```text
T T^*=F,
rank(F)=rank(E_-)=rank(E_+)=rank(P)/2.                   (JCF4)
```

This is the first literal occurrence package at the generation seam that
produces a genuine two-to-one matrix fold: it uses the balanced `S/T`
occurrence through `R` and the missing constant active-cycle incidence
through `b`.  The fold alone is not contradictory; coisometries from a
larger source to a smaller target exist.  To reach the sparse PI endpoint
one must still prove that the **same** `T` intertwines the compressed
degree-two source tuple with the literal degree-four target tuple.

The occurrence audit reduces the **relative discrepancy between the two
folded branches** to one row.  The
root `b` commutes with `X_0=x_12(Q)`, `X_1=x_14(Q)`, and `Z_1=x_43(1)`, while

```text
b x_23(1)b^(-1)=x_13(1)x_23(1).                          (JCF5)
```

On `P`, the extra factor is `x_13(1)=-x_13(ST)`.  Thus the sole relative
branch gauge is the tail-center `x_13(ST)`; controlling it requires an
additional occurrence (naturally the remaining opposite root), and is not
asserted here.  Even after that relative gauge is controlled, the absolute
identification of the transported tuple with the literal native target must
still be proved separately.

DERIVATION
binary-jacobson-closing-root-fold-proof
