---
rg: 2
id: pauli-generator-average-has-inverse-linear-gap
kind: claim
title: The coordinate Pauli average has an exact inverse-linear commutant gap
distinct_from:
  quantum-expander-relative-commutant-rounding: that assumes a constant-degree constant-gap channel; this uses all coordinate Pauli generators and loses only the square root of the Clifford depth.
  toeplitz-head-jacobi-words-give-uniform-expanders: that constructs constant-gap normalizer words; this elementary channel has no normalizer or multiplicity-twist input.
---

Let `P_i,Q_i`, `1<=i<=n`, be the standard Pauli generators of
`M_(2^n)` and let

```text
E:M_(2^n) tensor M_r -> I tensor M_r
```

be the trace-preserving conditional expectation.  For every matrix `Y`,

```text
||Y-E(Y)||_2^2
 <= (n/2)(1/(2n)) sum_(i=1)^n
       (||[Y,P_i tensor I]||_2^2+||[Y,Q_i tensor I]||_2^2).       (PAG1)
```

The constant is independent of `r`.  Consequently, if `x` is a contraction
in `M_(2^n) tensor I` and `y` is a contraction, then

```text
|tr(xy)-tr(x)tr(y)|
 <= sqrt(n/2)
    ((1/(2n))sum_i(||[y,P_i]||_2^2+||[y,Q_i]||_2^2))^(1/2).       (PAG2)
```

If `x` is only `eta`-close to the old spin factor, add `2 eta` to the
right-hand side.  Thus a polynomial-depth contraction ledger does not need a
constant-degree quantum expander: the coordinate Pauli checks cost only
`sqrt(n)`, which remains summable against a geometric return coefficient.

