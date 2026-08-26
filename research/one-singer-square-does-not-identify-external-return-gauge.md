---
rg: 2
id: one-singer-square-does-not-identify-external-return-gauge
kind: claim
title: One Singer square does not identify the closest external return gauge with the Whitehead gauge
invalidates:
  - external-8-to-7-one-singer-square-cancels-whitehead-gauge
artifacts:
  - research/external-return-singer-groupoid-gauge-proof.md
distinct_from:
  signed-hecke-normalizer-has-eight-external-root-returns: that constructs the eight external returns and leaves their multiplicity involutions uncontrolled; this chooses the return on the literal Whitehead coordinate pair and computes exactly what one Singer transport does to its involution.
  native-whitehead-hecke-head-has-order-seven-anchor: that gives an odd sevenfold loop detecting the Whitehead gauge when the active cut inherits the whole loop; this shows that a single source-to-target covariance square containing the external return is only conjugacy transport and does not identify its gauge with the Whitehead gauge.
  finite-extraspecial-mixed-words-cannot-ungauge-singer-transport: that treats quotient gauges in arbitrary finite normal extraspecial enlargements; this is a two-object carrier calculation for one explicit nonidentity signed-Hecke normalizer.
---

**ESTABLISHED ONE-SQUARE GAUGE NO-GO.**  Choose the external signed-Hecke
normalizer

```text
n=x_78(1),                                             (ESG1)
```

the arrow `8->7` in `(ERN2)`.  This is the closest of the eight returns to
the first literal Whitehead

```text
J=J_1=x_87(x_1)x_78(y_1)x_87(x_1),                    (ESG2)
```

because both use the same coordinate pair `(7,8)`.  Let

```text
Q=e_(L_0,lambda_0),      Q'=JQJ^(-1),
n'=JnJ^(-1).                                             (ESG3)
```

Since `n` normalizes the signed pair, it reduces `Q`; `n'` reduces `Q'`.
On the one-character source and target carriers choose fixed label charts.
Schur decomposition then has the form

```text
n|_(QH)=N_n tensor E,
J|_(QH)=N_J tensor D,
n'|_(Q'H)=N_(n') tensor E',                            (ESG4)
```

where `E` is precisely the external-return multiplicity involution and `D`
is the literal Whitehead gauge.  The exact one-step covariance is

```text
Jn=n'J.                                                (ESG5)
```

After removing the fixed label operators, `(ESG5)` says only

```text
E'=DED^(-1).                                           (ESG6)
```

It does not say `E=D`.  The same conclusion holds if the Singer head
`t_1=Jv_1` is used instead of `J`: the source normalizer `v_1` merely
changes the source chart, and the transported external gauge is conjugated
by the total transition gauge.

This independence is exact, not an artifact of estimates.  On the
four-dimensional multiplicity space put

```text
D=Z tensor I,             E=I tensor Z,                (ESG7)
```

where `Z=diag(1,-1)`.  Then `D,E` are commuting involutions, set `E'=E`,
and every relation `(ESG4)--(ESG6)` is exact, while

```text
||E-D||_2=sqrt(2).                                     (ESG8)
```

Thus neither the fact that `n` uses the Whitehead coordinate pair nor its
single Singer covariance authenticates gauge cancellation.  A successful
relation must form a genuinely mixed closed loop on one carrier in which
the external-return gauge and Whitehead gauge occur with unequal odd
parity; a transported conjugacy square is tautological.

This does not refute the use of `n=x_78(1)` together with an additional
full-EL20 mixed occurrence or with a compression of the sevenfold anchor.
It refutes only cancellation inferred from normalization, coordinate
overlap, and one Singer move.

No Property `(T)`, trace profile, approximation theorem, or
von-Neumann-algebra extension is used.

DERIVATION
external-return-singer-groupoid-gauge-proof

