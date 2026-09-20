---
rg: 2
id: fpbs-bs-via-stationary-set-relative-gap
kind: route
title: Certify nonuniqueness by almost surely finite visits of an independent walk range or subrelation class to the slightly supercritical cluster
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-stationary-set-relative-gap-universal
  - fpbs-stationary-set-recurrence-separates
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

Let `G` be a nonamenable Cayley graph.

1. By `fpbs-stationary-set-relative-gap-universal`, there are `p > p_c(G)`
   and an independent stationary set `A` with `V < infinity` a.s. under `P_p`.
2. By `fpbs-stationary-set-recurrence-separates`, `p_c(G) < p <= p_u(G)`. ∎

**Design notes.**

* **Compared with nearby routes.**
  * `fpbs-universal-green-visit-route` needs finite expected visits of simple
    random walk. This route needs only a.s. finite visits along some
    independent stationary set, and its hole is implied by that route's hole
    (`fpbs-stationary-set-gap-from-green-visit`).
  * `fpbs-bs-via-percolation-schreier-kesten-split` splits groups by whether a
    deterministic subgroup can carry a gap, and its second half admits no
    relative method.

* **Weakest hole.** The hole is implied by the green-visit kernel, by every
  subgroup relative gap, and by uniform connectivity decay past `p_c`
  (Section 6 of the artifact). So it is at least as weak as the hole of every
  route through those kernels.
* **No periodic-kernel barrier.** Split routes by subgroups are empty on the
  all-subgroups-co-amenable class. This route's random sets exist on every
  group.
* **What a proof must use.** By
  `fpbs-soft-collapse-kills-stationary-set-gap-proofs`, a proof of the hole must
  use a supercritical Bernoulli property.
