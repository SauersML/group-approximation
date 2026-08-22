---
rg: 2
id: finite-row-mask-group-algebra-certificate-forces-nonhyperlinear
kind: claim
title: A finite row-mask certificate in an ordinary group algebra forces nonhyperlinearity
distinct_from:
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that embeds the whole BCS algebra into one positive group-algebra corner; this needs only one global BCS tuple and independent high-density masks for its finitely many rows.
  nonhyperlinear-group-has-finite-canonical-microstate-witness: that extracts a finite witness after a group is known nonhyperlinear; this gives a concrete sufficient algebraic certificate which implies nonhyperlinearity and hence activates that compactness theorem.
  algebraic-bcs-corner-has-relator-energy-decoder: that decodes one common algebraic corner; this has no common corner or common Gram projection.
---

**ESTABLISHED CONDITIONAL PAYMENT.**  Let `Gamma` be an ordinary discrete
group and fix a finite BCS game of finite-dimensional gap `Delta>0`.  Suppose
`C[Gamma]` contains finitely supported elements

```text
P_(c,a), B_x, q_c^pred, q_(c,x)^con                    (RMC1)
```

such that the `P_(c,a)` form one PVM per context, the `B_x` are one global
family of self-adjoint involutions, the `q` are projections, and

```text
F_c q_c^pred=0,
(A_(c,x)-B_x)q_(c,x)^con=0.                            (RMC2)
```

If the canonical group trace satisfies

```text
D_row=sum_c mu_c tau_Gamma(1-q_c^pred)
      +sum_(c,x)mu_(c,x)tau_Gamma(1-q_(c,x)^con)
      <Delta,                                          (RMC3)
```

then `Gamma` is nonhyperlinear.

Moreover the supports of `(RMC1)--(RMC2)` and the finite multiplication
closure needed to evaluate them determine a finite symmetric window
`F subset Gamma` and an `epsilon_0>0`, independent of matrix dimension, on
which canonical multiplication and trace defect is at least `epsilon_0`.
Common amplification preserves that obstruction exactly.

This is a sufficiency theorem, not a construction of `(RMC1)`.  It is
strictly weaker than realizing the entire no-CE BCS algebra in one corner:
every verifier row may use its own mask.  What cannot vary rowwise is the
underlying context PVM or the shared involution `B_x`.

