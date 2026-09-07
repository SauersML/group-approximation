---
rg: 2
id: dimension-descent-criterion-proof
kind: route
title: An involution that survives is two away from the identity, and dimensions are well ordered
target: dimension-descent-criterion-for-non-mf
requires: []
artifacts:
  - research/artifacts/dimension-descent-criterion-2026-09-07.md
---

## Proof

Let `rho : G -> U(Q_d)` be a corona homomorphism with `rho(z) != 1`, and
lift the generators to unitaries `U^((n)) in U(d_n)^k`, which is possible by
polar decomposition in the finite von Neumann algebra `prod_n M_(d_n)`.
Every `r in R` is a relation of `G`, so `delta(U^((n))) -> 0`.

Put `w_n = z(U^((n)))`.  Since `z^2 in R`, `||w_n^2 - I|| -> 0`, so every
eigenvalue `lambda` of `w_n` satisfies `|lambda^2 - 1| -> 0` uniformly and
therefore lies near `1` or near `-1`.  Since `rho(z) != 1`,
`||w_n - I||` does not tend to zero, so along a subsequence some eigenvalue
lies near `-1`, and there `||w_n - I|| -> 2`.

Fix `n` in that subsequence, large enough that `delta(U^((n))) < epsilon_0`
and `||w_n - I|| >= 1`.  The set of dimensions `d` admitting a tuple with
both properties is then a nonempty set of positive integers; take its least
element and a witnessing tuple, and apply the operation.  It returns a tuple
in a strictly smaller positive dimension with both properties, contradicting
minimality.

So no corona homomorphism is nontrivial on `z`, which says `z` is in the MF
residual.  A countable group all of whose corona homomorphisms kill a
nontrivial element is not MF, since an MF group embeds in the unitary group
of a norm matrix corona.  The MF residual is normal, so if `z` normally
generates `G` it is all of `G`.
