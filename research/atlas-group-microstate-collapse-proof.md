---
rg: 2
id: atlas-group-microstate-collapse-proof
kind: route
title: Traces of a regular representation are delta functions, so both energies read off one stabilizer
target: atlas-group-microstate-collapse-is-subgroup-containment
requires: []
artifacts:
  - experiments/atlas_asc_countermodel_energy.py
  - experiments/asc-countermodel-energy.json
---

Let `U = lambda_E(mu)`.  Then `rho(x)U = lambda_E(alpha(x) mu alpha(x)^(-1))`
is again a group element, so

```text
<U, rho(x)U> = tr( lambda_E( mu^(-1) . (x . mu) ) ) = delta(x . mu = mu),
```

because in a regular representation `tr(lambda(h)) = delta_(h,e)`.  Hence
`<U, rho(x)U> = delta(x in Z)` with `Z = Stab(mu)`, and both quadratic forms
evaluate by summing their integer coefficients over `Z`:
`sum_s l_s^2 = E(Z)` and `a^2+b^2 = 4 - 2[h_a in Z] - 2[h_b in Z]`.  Word
defects are `2 - 2 delta(value = e)`, hence `0` or `2`.

For the collapse criterion: `rho(x)U = U` iff `x . mu = mu` iff `x in Z`, so
`U` lies in the `H`-fixed space -- which is `ker rho(W_pkt)`, of dimension
`120 = [A_8 : H]` -- exactly when `H <= Z`.  Positivity of `rho(W_pkt)` gives
`E(Z) >= 0` for every subgroup, with equality precisely in that case, and
`h_a, h_b in H` then forces the covariance to vanish.

The characteristic-two countermodel instantiates all of it: `mu = (m, e)`,
`Z = { x : (1+x)m = 0 } = { x : 1+x in I }`, computed by closing the 234
boundary derivatives under left translation (rank 20005, empty queue, an
independent reproduction of the rank-three audit).  Neither raw `S_3` letter
lies in `Z`, only 3 of the 101 support elements of `W_pkt` do, and
`E(Z) = 1372`.
