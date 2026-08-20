---
rg: 2
id: expander-factor-trace-independence-proof
kind: route
title: Conditional expectation factorizes the trace after expander rounding
target: expander-separated-factors-have-independent-traces
requires:
  - quantum-expander-relative-commutant-rounding
---

Let `E:M_N tensor M_r -> I_N tensor M_r` be the trace-preserving conditional
expectation.  Since `x` lies in `M_N tensor I_r`, tensor-product trace gives

```text
tr(x E(y))=tr(x)tr(E(y))=tr(x)tr(y).                    (1)
```

Therefore Cauchy--Schwarz and `||x||_2<=1` give

```text
|tr(xy)-tr(x)tr(y)|
 =|tr(x(y-E(y)))|
 <=||y-E(y)||_2.                                       (2)
```

Apply `(QEC1)` from
`quantum-expander-relative-commutant-rounding` to obtain `(ESF1)`.
If `x_0` is a spin-factor contraction with `||x-x_0||_2<=eta`, replace `x`
by `x_0` in the two trace terms.  Each replacement costs at most `eta`,
giving the stated `2 eta` addendum.
