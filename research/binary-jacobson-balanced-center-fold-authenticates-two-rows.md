---
rg: 2
id: binary-jacobson-balanced-center-fold-authenticates-two-rows
kind: claim
title: The balanced Jacobson center has an exact orthogonal fold and authenticates both Q-rows
artifacts:
  - research/binary-jacobson-balanced-center-fold-proof.md
distinct_from:
  binary-jacobson-balanced-target-redesign-contains-mixed-root: that computes the redesigned packet and proves its center carries the raw range off itself; this turns that orthogonality into an exact coisometry onto a negative moved-center cut.
  binary-jacobson-closing-root-folds-head-two-to-one: that folds two source sign sectors onto one raw range using the closing constant root; this folds one raw range and its moved-center image onto the negative center carrier of the mixed target packet.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for all four degree-two-to-degree-four covariance rows; this proves the carrier identity and the two Q-labelled rows, leaving exactly the two T-labelled rows.
---

**ESTABLISHED.**  Let `e=F_+`, and let

```text
c_T=I+QT E_11,
D_T=(x_12(Q),x_21(T),x_14(Q),x_41(T))
```

be the balanced target packet of
`binary-jacobson-balanced-target-redesign-contains-mixed-root`.  Put

```text
e'=c_T e c_T,       E=e+e',
q=E(1-c_T)/2,       V=(1-c_T)e/sqrt(2).                 (JCF1)
```

Then `e` and `e'` are orthogonal, `E` commutes with `c_T`, and `q` is a
projection in the negative `c_T` cut.  The literal occurrence `V` is an
exact coisometry from `e` onto `q`:

```text
V^*V=e,             VV^*=q.                             (JCF2)
```

Moreover the two Q-labelled generators preserve both carriers and satisfy
the exact covariance rows

```text
x_12(Q)V=V x_12(Q)|_e,
x_14(Q)V=V x_14(Q)|_e.                                  (JCF3)
```

Thus the moved-center carrier is not an open selection problem: it is
canonically and dimension-independently authenticated by `(JCF1)`.  Exactly
two rows remain for the redesigned packet,

```text
x_21(T) V = V C_2,       x_41(T) V = V C_4,             (JCF4)
```

for one common degree-two source tuple on `e`.  The first T-root is the
already audited half-supported alternating polar; the second is a new
opposite-coordinate T-root.  Closing `(JCF4)`--or proving that the two T-root
leakages have complementary supports--would authenticate the full literal
M4 target without returning to the old fixed tuple `D`.

DERIVATION
binary-jacobson-balanced-center-fold-proof
