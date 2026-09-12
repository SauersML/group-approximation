---
rg: 2
id: modular-vertex-chart-control-from-central-splitting
kind: route
title: Split the central involution, average the residual cyclic cocycles, and differentiate unitary exponentials
target: modular-vertex-charts-have-uniform-schatten-control
requires: []
artifacts:
  - research/artifacts/modular-vertex-admissible-charts-2026-09-08.md
---

For a cocycle `c`, put `P_Z=(I+Ad Z)/2`. The explicit lift is

```text
H_0=c(z)/2,
H_4=P_Z c(s)/2,
H_6=(P_Z c(b)-Ad(B^-1)P_Z c(b))/3.
```

Centrality and `z^2=1` give
`c(g)-delta(H_0)(g)=P_Z c(g)` for every `g`.
The residual cyclic equations are order two for `s` and order three
for `b`, giving exactly `delta(H_4)(s)=P_Z c(s)` and
`delta(H_6)(b)=P_Z c(b)`. Conditional averaging is contractive in
every normalized Schatten norm; `c(z)=c(s)+Ad(S)c(s)` gives the
constant-one upper lift estimate. The derivative of the explicit
parameterization has norm at most four, giving the lower estimate and
the tuple-flatness transfer.

Each generator in the parameterization is conjugated twice. The inner
conjugations commute with `Z`, so both central powers remain the same
outer conjugate of `Z`; all vertex relations hold exactly.

The ordered-simplex formula for the `j`th derivative of `exp(H)` is a
sum of `j!` integrals, each over a simplex of volume `1/j!`, containing
unitaries separated by the `j` direction matrices. Normalized Schatten
Hoelder gives the product of the input norms with no dimension or
operator-norm cost. A length-`ell` word has at most `4 ell` exponential
slots, so assigning each derivative direction to a slot gives
`(4 ell)^j`. Integrating the first derivative gives the movement bound.

The artifact supplies the full cocycle calculations, derivative formula,
pair extension, and the precise remaining quadratic-repair obligations.
No computational or external arithmetic input is needed.
