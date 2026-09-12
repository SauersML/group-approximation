---
rg: 2
id: expander-separated-factors-have-independent-traces
kind: claim
title: A quantum-expander-separated tensor factor has dimension-free trace independence
distinct_from:
  quantum-expander-relative-commutant-rounding: that bounds distance to the relative commutant; this converts that bound into the scalar covariance estimate needed by the squaring ledger.
---

Let `Phi` be a random-unitary channel on `M_N` with traceless
Hilbert--Schmidt norm at most `lambda<1`, implemented by
`U_1,...,U_D`.  On `M_N tensor M_r`, let `x` be a contraction in
`M_N tensor I_r` and let `y` be any contraction.  Then

```text
|tr(xy)-tr(x)tr(y)|
 <= (1/(1-lambda))
    ((1/D)sum_j ||[y,U_j tensor I_r]||_2^2)^(1/2).       (ESF1)
```

The constant is independent of `N` and `r`.  If `x` is only `eta`-close to
the spin factor, the right side increases by at most `2 eta`.
