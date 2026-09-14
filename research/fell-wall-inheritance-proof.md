---
rg: 2
id: fell-wall-inheritance-proof
kind: route
title: Expand in group coordinates; equivariance plus square summability kills every nontrivial coordinate
target: fell-models-inherit-walls-from-coefficients
requires: []
---

Put `P = L(G) tensor-bar M_0` with the product trace, and let
`E : P -> M_0` be the trace-preserving conditional expectation
`E(lambda_h tensor b) = delta_(h,e) b`.

**Step 1 (Fourier coordinates).** Every `x in P` has the `||.||_2`-convergent
expansion `x = sum_h lambda_h tensor b_h` with `b_h = E((lambda_h^* tensor 1) x)`,
and `||x||_2^2 = sum_h ||b_h||_2^2`.

**Step 2 (commutation is equivariance).** For `gamma in Gamma`,

```text
sigma(gamma) x sigma(gamma)^* = sum_h lambda_(gamma h gamma^(-1)) tensor pi(gamma) b_h pi(gamma)^*.
```

By uniqueness of the coordinates, `x` commutes with `sigma(Gamma)` iff
`b_(gamma h gamma^(-1)) = pi(gamma) b_h pi(gamma)^*` for all `gamma, h`.

**Step 3 (only the identity coordinate survives).** On a commuting `x`,
`||b_h||_2` is constant along each `Gamma`-conjugacy class. Every class of an
element `h != e` is infinite, and `sum_h ||b_h||_2^2 < infinity`, so `b_h = 0`
for `h != e`. Then `x = 1 tensor b_e`, and Step 2 with `h = e` says
`b_e in pi(Gamma)'`. Conversely `1 tensor b` commutes with `sigma(Gamma)`
whenever `b in pi(Gamma)'`. This is the first identity in `(FMW1)`.

**Step 4 (the action).**
`sigma(g)(1 tensor b)sigma(g)^* = lambda_g lambda_g^* tensor pi(g) b pi(g)^* = 1 tensor pi(g) b pi(g)^*`.

**Step 5 (conjugate subgroups and consequences).** `h` has infinite
`t Gamma t^(-1)`-class iff `t^(-1) h t` has infinite `Gamma`-class, so Steps 1--4
also apply to `t Gamma t^(-1)`. A relative wall for `sigma` is an element of
`P cap sigma(t Gamma t^(-1))'` outside `P cap sigma(Gamma)'`. By `(FMW1)` for both
subgroups, these are `1 tensor b` with `b` a wall for `pi`, and conversely.
Stabilizers agree by Step 4.
