---
rg: 2
id: nonhyperlinear-sep7-osgood-extraction-proof
kind: route
title: Compare the finite dimension ledger with a scalar Osgood flow
target: nonhyperlinear-sep7-osgood-extraction
requires:
  - sequential-exact-corner-extraction-has-quadratic-error-ledger
artifacts:
  - research/artifacts/nonhyperlinear-sep7-osgood-extraction.md
---

Use the required ledger with
`A_i=d^(-1)sum_(l<i)xi_l^2 r_l` and
`y_i=delta_0^2+3 ell^2 A_i`. Relator telescoping gives
`delta(U^(i))^2<=2y_i/x_i`, where `x_i=n_i/d` is the remaining
dimension fraction. While `x_i>theta`, each extraction obeys

```text
y_(i+1)<=y_i+3 ell^2 psi(2y_i/theta)(r_i/d).
```

The total clock `sum_i r_i/d` is at most one, including the last
cut crossing the dimension threshold. The increasing scalar flow
with derivative `3 ell^2 psi(2y/theta)` dominates this finite Euler
recursion. The Osgood integral divergence makes its value at time
one tend to zero with `delta_0`. Induction simultaneously verifies
the seed threshold on every residual; it is not assumed in advance.

The algorithm stops after at most d cuts. A residual of size at most
`theta d` is replaced by the trivial representation at squared cost
at most `3A+4theta`; an exact residual has cost at most `3A`; a full
flexible residual correction has global squared cost at most
`6A+2psi(delta_residual^2)` and padding at most
`psi(delta_residual^2)`. First take the initial defect to zero at fixed
theta, then theta to zero. These are uniform correction estimates.

For the logarithmic modulus, switch to clock `r_i/n_i`. Its total is
at most `1+log(1/theta)`, and the scalar equation is
`y'=6K ell^2 y log(e/y)`. Its explicit solution and the choice
`theta=log(e/delta_0^2)^(-1/(12K ell^2))` give the stated rates.
The artifact supplies the full recurrence, all stopping cases, and
the admissibility induction.
