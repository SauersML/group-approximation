---
rg: 2
id: fanizza-heat-filter-cstar-decay-proof
kind: route
title: Functional calculus proves uniform decay of the Fanizza heat filters
target: fanizza-heat-filter-has-uniform-cstar-decay
requires:
  - two-copy-bcs-game-hamiltonian-dominates-fanizza-signal
---

Fix a nonmember `m`, a unitary representation `pi`, and suppress `pi` from
the notation.  The established two-copy Hamiltonian theorem gives

```text
0 <= D_R <= C_m H_m,       0 <= H_m <= 1.
```

Put `K_m=1-H_m`.  Since `D_R` is a projection, multiplication of the
operator inequality on both sides by `K_m^t` gives

```text
||D_R K_m^t||^2
 = ||K_m^t D_R K_m^t||
 <= C_m ||K_m^t H_m K_m^t||.
```

The last three factors commute.  Continuous functional calculus therefore
identifies the last norm with the maximum of
`lambda(1-lambda)^(2t)` on `[0,1]`.  Its critical point is
`lambda=1/(2t+1)`, and its value is at most `1/(2t+1)`.  This proves

```text
||pi(D_R K_m^t)|| <= sqrt(C_m/(2t+1))
```

uniformly over all representations.

For the accelerated filter put `x=1-2lambda`.  The Chebyshev identity

```text
(1-x^2) U_(t-1)(x)^2 <= 1,       x in [-1,1],
```

and the definition
`p_t(lambda)=((1-lambda)/t)U_(t-1)(1-2lambda)` give

```text
lambda |p_t(lambda)|^2
 = (1-lambda)(1-x^2)U_(t-1)(x)^2/(4t^2)
 <= 1/(4t^2).
```

Repeating the preceding order argument with `p_t(H_m)` in place of
`K_m^t` yields

```text
||pi(D_R p_t(H_m))|| <= sqrt(C_m)/(2t).
```

All coefficients are rational because `H_m` is rational and `U_(t-1)` has
integer coefficients; also `p_t(0)=U_(t-1)(1)/t=1`.

On the member side, the perfect vector `xi` from the two-copy theorem obeys
`H_m xi=0` and `D_R xi!=0`.  Hence `K_m^t xi=xi` and
`p_t(H_m)xi=xi`, so both filtered elements act as `D_R` on `xi` and are
nonzero.  This proves every clause of the target claim.
