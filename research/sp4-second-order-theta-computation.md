---
rg: 2
id: sp4-second-order-theta-computation
kind: route
title: Solve the four-by-four theta transformation matrices from minor equations and fit the relator scalars to the lift pattern
target: sp4-second-order-thetas-realize-metaplectic-class-in-dim-four
requires: []
artifacts:
  - experiments/maslov_sector/theta2b.py
  - experiments/maslov_sector/theta2b.log
---

The four functions are evaluated by the lattice sum over `|n_i| <= 8` at
eight random points of `H_2` with imaginary part near the identity.  For a
generator `s` the condition that `Theta(s tau)` be parallel to
`M Theta(tau)` is linear in the sixteen entries of `M` once written as the
vanishing of the six `2 x 2` minors of the pair; forty-eight equations at
eight points have a one-dimensional null space (second singular value
`3e-3`, smallest `1e-16`), and the null vector is unitary up to scale.  The
polar unitary part is taken.  Relator products are computed in batches by
length; the phase of each scalar is compared with `(-1)^{k_r}` by fitting
eight generator phases (BFGS, sixty random starts, four thousand relators)
and the fit is then verified on all `304,412` relators to `8e-8`.  The same
fit against the trivial pattern fails with residual `2`, which is the
computational meaning of "the class is not trivial"; that it is
metaplectic rather than some other class is the equality with the lift
exponents on the twenty lifted relators, where the two patterns differ.
