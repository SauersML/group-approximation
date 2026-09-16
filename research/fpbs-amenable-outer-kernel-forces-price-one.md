---
rg: 2
id: fpbs-amenable-outer-kernel-forces-price-one
kind: claim
title: If an infinite amenable group of quotient elements acts on an infinite normal subgroup by inner automorphisms, the group has fixed price one
distinct_from:
  fpbs-wq-normal-price-one-subgroup-forces-price-one: that transfers fixed price one upward from a given infinite wq-normal subgroup; this manufactures such a subgroup, an infinite amenable normal subgroup of a preimage, out of quotient elements acting by inner automorphisms, and is proved through that claim.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that is the open statement assuming bounded action cost on the normal subgroup; this assumes no cost bound and instead needs an infinite amenable subgroup in the kernel of the outer action of the quotient.
artifacts:
  - research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md
---

**Statement.** Let `N` be an infinite normal subgroup of a countable group
`Gamma`, and let `rho : Gamma/N -> Out(N)` be the outer action. Suppose
`ker rho` contains an infinite amenable subgroup `A`. Then `Gamma` has fixed
price one. No cost hypothesis on `N` is needed.

**Consequences.**
- **Semidirect products.** `N semidirect_phi Z` has fixed price one when `N`
  is infinite and `phi` has finite order in `Out(N)`. The outer kernel is
  `kZ`.
- **Locally finite quotients.** `Gamma` has fixed price one when `Gamma/N` is
  locally finite and `ker rho` is infinite.

These remove the finite-order monodromy case and the infinite-inner-part
cases from `fpbs-normal-subgroup-bounded-cost-fixed-price-one`. That is the
Case 0 of `fpbs-bounded-cost-normal-via-quotient-trichotomy`.
