---
rg: 2
id: fpbs-infinite-centralizer-forces-price-one
kind: claim
title: An infinite normal subgroup with infinite centralizer forces fixed price one, so every infinite outer kernel does
distinct_from:
  fpbs-amenable-outer-kernel-forces-price-one: that needs an infinite amenable subgroup in the kernel of the outer action; this needs only that the kernel, or equivalently the centralizer of the normal subgroup, is infinite, and it is proved through Khezeli's product theorem.
  fpbs-khezeli-products-have-fixed-price-one: that covers direct products of two infinite groups; this covers every group with two commuting infinite normal subgroups, whose product need not split as a direct product and need not be the whole group.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that assumes bounded action cost on the normal subgroup and allows a trivial centralizer; this assumes no cost bound but needs an infinite centralizer.
artifacts:
  - research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md
---

**Statement.** Let `N` and `M` be infinite normal subgroups of a countable
group `Gamma` that commute elementwise. Then `Gamma` has fixed price one.

Equivalently, let `N ◁ Gamma` be infinite with `C_Gamma(N)` infinite. Then
`Gamma` has fixed price one. No cost hypothesis is needed.

**Special cases.**
- **Infinite outer kernel.** If the kernel `Q_0` of the outer action
  `Gamma/N -> Out(N)` is infinite, then `Gamma` has fixed price one. Indeed
  `Q_0 = pi(C_Gamma(N))`, a quotient of `C_Gamma(N)`.
- **Infinite center.** If `Z(N)` is infinite, the same holds. This case was
  already known.
- **Commuting modulo a finite subgroup.** If `[N, M]` is finite, the same
  holds. Pass to `Gamma/[N, M]`, then lift across the finite kernel with
  `fpbs-finite-normal-quotient-lifts-price-one`. This is Corollary C.2 of the
  linked artifact.

**Consequences.**
- In `fpbs-bounded-cost-normal-via-quotient-trichotomy`, Case 0 extends from
  an outer kernel containing an infinite amenable subgroup to every infinite
  outer kernel.
- The "Commuting part of the outer kernel" attempt on
  `fpbs-bounded-cost-fg-torsion-quotient-price-one` is completed. It is not
  needed to pass from `N x C` to a finite central quotient. One uses the
  direct product `NC/Z` with `Z = N ∩ C`, and lifts across the finite kernel
  `Z`.
