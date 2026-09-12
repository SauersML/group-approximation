---
rg: 2
id: fpbs-quotient-split-actions-have-cost-one
kind: claim
title: A free action factoring onto a free finite-cost quotient action has cost one when the normal subgroup has bounded action cost
distinct_from:
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that asserts cost one for every free action of the group; this proves it only for actions admitting a free finite-cost factor of the quotient group, which the Bernoulli shift never admits.
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

**Theorem A of the linked note.** Let `N` be an infinite normal subgroup of a
countable group `Gamma` with `Q = Gamma/N` infinite, and suppose every
essentially free p.m.p. action of `N` has cost at most `K < infinity`. Let
`alpha` be an essentially free p.m.p. action of `Gamma` on `(X,mu)`, and
`phi : X -> Y` a `Gamma`-equivariant factor map onto an essentially free
p.m.p. action `sigma` of `Q` of finite cost, with `Gamma` acting on `Y`
through the quotient. Then `C(alpha) = 1`.

**Proof outline.**
* Take a complete section `A` of the quotient orbit relation with
  `nu(A) <= delta`, and set `B = phi^(-1)(A)`. The set `B` is `N`-invariant
  and meets every orbit.
* Use the bounded `N`-cost only on `B` (cost at most `(K+epsilon) delta`).
* Attach every point outside `B` to `B` by one edge (cost at most one).
* Connect the `N`-orbits inside `B`, which correspond bijectively to points of
  `A` within each orbit by freeness of `sigma`. Lift a graphing of the induced
  quotient relation only at a Borel complete section `S` of the `N`-relation
  whose conditional measure on every fibre is at most `eta` (marker lemma).
  This costs at most `eta (C(sigma) + epsilon)`.
* The union generates, so `C(alpha) <= 1 + (K+epsilon) delta + eta (C(sigma)+epsilon)`.

**Consequence.** For every free action `beta` of `Gamma` and every free
finite-cost action `sigma` of `Q`, the diagonal action `beta x sigma` has cost
one. So `cost(Gamma) = 1`, which is Gaboriau's normal subgroup theorem for
infimal cost under the uniform hypothesis. The hypothesis holds for finitely
generated `N` with `K = d(N)`, and for every infinite subgroup of a large odd
free Burnside group with `K = 2` by `fpbs-burnside-common-upper-cost`.

**Scope.** This does not give fixed price one.
`fpbs-quotient-split-not-bernoulli-contained` shows that no action of this kind
is weakly contained in the Bernoulli shift when `N` is nonamenable, so the
theorem cannot be transferred to the maximal-cost action by weak containment.

Status records a written deduction over the named inputs, not an independent
verification or a formal proof.
