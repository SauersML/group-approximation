---
rg: 2
id: fpbs-mal-infinite-index-normal-subgroups-cost-infinity
kind: claim
title: Every nontrivial normal subgroup of infinite index in Gamma_mal, such as the normal closure of a, has infinite first L2-Betti number, so every free action of it, and every restriction of a free Gamma_mal-action to it, has infinite cost
distinct_from:
  fpbs-finite-cost-normal-subgroup-infimal-cost-one: that is the general imported theorem that finite infimal cost of a normal subgroup of infinite index forces infimal cost one; this applies it (and Gaboriau's L2 theorem) to Gamma_mal to show that every such subgroup is infinitely expensive, which kills normal-subgroup transfer at Gamma_mal.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that is an open fixed-price-one criterion with a bounded-cost hypothesis; this shows the hypothesis never holds for infinite-index normal subgroups of Gamma_mal.
  fpbs-mal-bernoulli-single-stage-floor: that is the open floor; this is a class-kill for routes to it and decides nothing about it.
artifacts:
  - research/artifacts/fpbs-mal-normal-and-intermediate-class-kills-2026-09-20.md
---

**ESTABLISHED** through `fpbs-mal-infinite-index-normal-subgroups-cost-infinity-proof`.

Let `1 != Λ ⊴ Gamma_mal` have infinite index. Then:
- `beta_1^(2)(Λ) = infinity`;
- every free p.m.p. action of `Λ` has infinite cost;
- in particular, `C(α|Λ) = infinity` for every free action `α` of
  `Gamma_mal`.

Such subgroups exist:
- `χ(a) = 0`, `χ(b_k) = (-1)^{k+1}` defines `Gamma_mal ->> Z`;
- its kernel is the normal closure `<<a>>`, so `Gamma_mal = <<a>> ⋊ <b_1>`;
- `<<a>>` is the union of the infinite-rank free groups `<<a>> ∩ H_n`.

**Consequence.** Normal-subgroup cost transfer is inert at `Gamma_mal`:
- upper bounds of the form `C(α) <= C(α|Λ)` read `C(α) <= infinity`;
- the bounded-cost fixed-price-one criteria never apply.

The obstruction is L2 and not finite generation.
