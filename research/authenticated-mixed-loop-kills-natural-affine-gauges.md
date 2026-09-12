---
rg: 2
id: authenticated-mixed-loop-kills-natural-affine-gauges
kind: claim
title: The authenticated mixed denominator loop kills every natural affine gauge
artifacts:
  - research/authenticated-mixed-loop-natural-affine-proof.md
distinct_from:
  one-mixed-denominator-a2-loop-is-dyadic-tower-neutral: that finite wreath model satisfies the mixed loop and the closed A2 returns but deliberately violates the genuine conjugacy W_12 E_12 W_12^*=B_21; this tests the authenticated packet on the natural affine extension of an honest coefficient actor.
  rank-one-conjugacy-kills-c2-congruence-fold: that removes scalar C2 sheet characters; this removes a genuinely noncentral translation gauge in every number of copies of the natural coefficient module.
  rank-one-closure-excludes-noncentral-outlier-gauges: that asks for a dimension-free theorem for arbitrary unitary multiplicity gauges and noncongruence outliers; this proves only the natural affine semidirect-product sector and explicitly leaves general coefficient modules open.
---

Let `k` be any finite field of odd characteristic, let

```text
F=SL_3(k),                 M=k^3,
h=diag(2,1,1/2),           E=M rtimes F,               (AMG1)
```

where `F` acts naturally on column vectors.  Put every integral root and
Weyl coefficient in the copy `{0} rtimes F`, but allow the denominator lift
to carry an arbitrary natural affine gauge

```text
H=(lambda,h),              lambda in M.                (AMG2)
```

Impose, on this same carrier,

```text
[H x_21(-1) H^(-1),x_13(1)]=H^(-1)x_23(-1)H,          (AMG3)
R_tor=1.                                                  (AMG4)
```

The coefficient packet is the honest `SL_3(k)` packet, so both closed `A_2`
returns and the genuine rank-one conjugacy

```text
W_12 E_12 W_12^*=B_21                                 (AMG5)
```

hold exactly, as do all internal root and Weyl relations.  Then

```text
lambda=0.                                              (AMG6)
```

The assertion remains true for an arbitrary direct sum of natural modules:
the two word equations act componentwise, so they kill every natural affine
multiplicity gauge with no dependence on the number of summands.

Thus the first mixed denominator loop becomes a genuine gauge detector after
rank-one authentication: the obvious affine replacement for the residual
`C_2` sheet enemy does not exist.  This does **not** prove the full
noncentral-gauge terminal.  A surviving countermodel could use a different
`F`-module, a nonlinear extension, or a genuinely noncongruence actor
outlier.  Those are exactly the sectors still quantified over by
`rank-one-closure-excludes-noncentral-outlier-gauges`.

For clarity, in the arbitrary tensor-gauge notation of
`rank-one-closure-reduces-to-noncentral-gauge`, put

```text
U=PQP,               V=RTR,               C=[P,R].     (AMG7)
```

The rank-one conjugacy and two returns give

```text
UPU^*=Q,             URU^*=C=V^*PV.                   (AMG8)
```

The new mixed word and the torus word add exactly

```text
[GQG^*,C]=G^*R^*G,                                   (AMG9)
G=P^2GQG^*P^2U^* R^2GTG^*R^2V^*.                    (AMG10)
```

The natural-affine proof below shows that the corresponding two Fox rows
have zero common kernel on the defining module.  It does not assert that the
nonlinear unitary system `(AMG7)--(AMG10)` has only the trivial solution.
That exact distinction is the remaining noncentral-gauge leaf.

DERIVATION
authenticated-mixed-loop-natural-affine-proof
