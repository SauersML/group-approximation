---
rg: 2
id: fpbs-bounded-cost-outer-cyclic-extension-price-one
kind: claim
title: A cyclic extension of a bounded-cost group by an automorphism of infinite outer order has fixed price one
distinct_from:
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that allows any infinite quotient; this is its special case with quotient Z acting by an automorphism of infinite order in Out(N), and the trichotomy route shows the general case follows from this one together with the locally finite and finitely generated torsion cases.
  fpbs-twisted-level-graph-generates-cyclic-extension: that is an established generation criterion for one explicit transport graphing of a cyclic extension; this is the open fixed price one assertion for such extensions under a cost bound on the fiber.
  fpbs-hyperbolic-3-manifold-groups-fixed-price-one: that is the closed hyperbolic 3-manifold class; this is a statement about all bounded-cost cyclic extensions, and it implies that class through fpbs-hyperbolic-3-manifold-via-outer-cyclic-extension.
artifacts:
  - research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md
---

**OPEN.** Let `N` be a countably infinite group. Suppose there is
`K < infinity` such that every essentially free p.m.p. action of `N`, ergodic
or not, has cost at most `K`. Let `phi in Aut(N)` have infinite order in
`Out(N)`. Then `N semidirect_phi Z` has fixed price one.

**Scope.**
- This is case (a) of `fpbs-bounded-cost-normal-via-quotient-trichotomy`.
- The finite-order case is established by
  `fpbs-amenable-outer-kernel-forces-price-one`.
- It contains every fibered hyperbolic 3-manifold group, with
  `N = pi_1(S_g)` and pseudo-Anosov monodromy.

## Attempts

* **Quotient-split actions (Theorem A).** Theorem A gives cost one when the
  action factors onto a free `Z`-action through an `N`-invariant factor.
  **Where it dies:** in the Bernoulli shift `N` acts ergodically, so no such
  factor exists. This is the vertical-constancy obstacle of the parent claim.
* **Transport graphing through twisted level percolation.**
  `fpbs-twisted-level-graph-generates-cyclic-extension` turns generation of
  the Bernoulli orbit relation into connectivity of a random graph on `N`.
  **Where it dies:** that graph is disconnected at low density, which refutes
  `fpbs-twisted-level-percolation-connected`. The correlated replacement
  `fpbs-cross-line-correlated-transport-set-generates` is open.
* **Horoballs from Khezeli's product theorem.** **Where it dies:** the product
  metric on `N semidirect Z` is proper only when every conjugacy orbit in `N`
  is finite, by `fpbs-split-product-metric-needs-finite-conjugacy-orbits`.
  That fails for infinite outer order.
* **Slutsky's product-neighbourhood test and Bevilacqua--Bowen Theorem 8.1.**
  - Balls and cyclic sets fail Slutsky's test (Remark H of
    `research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md`).
  - The horosphere-type actions are not partially doubly recurrent
    (Proposition F of the same note).
  - `notes/fpbs-normal-subgroup-bounded-cost-fixed--swarm-2026-09-16.md`
    (Section 3, item 2) records an obstruction attempt using
    multiplicative energy and non-inner-amenability. **Where it dies:** it
    compares twisted and untwisted energies only up to a constant factor, so
    it neither excludes nor supplies test sets.
* **Change the monodromy by a power.** Replacing `phi` by `phi^k` gives a
  finite-index subgroup, and fixed price one passes up finite index. **Where
  it dies:** `phi^k` still has infinite outer order, so nothing is gained.
