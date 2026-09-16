---
rg: 2
id: fpbs-bounded-cost-fg-torsion-quotient-price-one
kind: claim
title: A bounded-cost normal subgroup with infinite finitely generated torsion quotient and no infinite amenable inner part forces fixed price one
distinct_from:
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that allows any infinite quotient; this is its special case with an infinite finitely generated torsion quotient whose outer kernel contains no infinite amenable subgroup.
  fpbs-burnside-upper-cost-one: that is the numerical assertion c_n=1 for large odd Burnside groups; this is a general extension statement, which implies it through fpbs-burnside-upper-cost-one-via-fg-torsion-quotient.
  fpbs-bounded-exponent-bounded-finite-subgroups-price-one: that concerns bounded-exponent groups with bounded finite subgroups and no normal structure; this assumes a bounded-cost infinite normal subgroup and an infinite finitely generated torsion quotient, with no exponent bound.
  fpbs-amenable-outer-kernel-forces-price-one: that established lemma needs an infinite amenable subgroup in the outer kernel; this assumes the outer kernel has none, so the lemma does not decide it, and the cost bound must be used.
artifacts:
  - research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md
---

**OPEN.** Let `N` be an infinite normal subgroup of a countable group
`Gamma`. Suppose every essentially free p.m.p. action of `N` has cost at most
some `K < infinity`. Suppose `Gamma/N` is infinite, finitely generated and
torsion, and the kernel of the outer action `Gamma/N -> Out(N)` contains no
infinite amenable subgroup. Then `Gamma` has fixed price one.

**Scope.**
- This is case (c) of `fpbs-bounded-cost-normal-via-quotient-trichotomy`.
- If the kernel contains an infinite amenable subgroup,
  `fpbs-amenable-outer-kernel-forces-price-one` gives the conclusion with no
  cost bound.
- The free Burnside split `B(m,n) = N semidirect B(m-1,n)` satisfies the
  hypotheses with `K = 2` and finite outer kernel. See
  `fpbs-burnside-upper-cost-one-via-fg-torsion-quotient`.

## Attempts

* **Quotient-split actions and weak containment.** Theorem A gives cost one
  for actions with a free finite-cost quotient factor. **Where it dies:**
  - Bernoulli shifts have no such factor.
  - The weak-containment upgrade is dead by
    `fpbs-quotient-split-not-bernoulli-contained`.
* **Commuting part of the outer kernel.**
  - Suppose the kernel `Q_0` is infinite. Since it has no infinite amenable
    subgroup, it has an infinite finitely generated subgroup `B_0`.
  - Its preimage is `N C`, where `C` centralizes `N`, `N ∩ C = Z(N)`, and
    `C/Z(N) ≅ B_0`.
  - If `Z(N)` is infinite, it is an infinite abelian normal subgroup and the
    group has fixed price one.
  - **Where it dies:** if `Z(N)` is finite, the preimage is a quotient of
    `N x C` by a finite central subgroup.
    - Khezeli's product theorem covers `N x C`.
    - The passage to the quotient is not established. The natural
      class-bijective extension bounds cost in the wrong direction, and lifting
      a free action to `N x C` needs a measurable splitting of a 2-cocycle.
  - When the kernel is finite, as for Burnside groups, nothing commutes and
    this approach gives nothing.
* **Horoballs from products.** **Where it dies:** by
  `fpbs-split-product-metric-needs-finite-conjugacy-orbits`, the product metric
  is proper only for finite conjugacy orbits. That fails for the Burnside
  split.
