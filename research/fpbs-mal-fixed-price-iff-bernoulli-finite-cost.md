---
rg: 2
id: fpbs-mal-fixed-price-iff-bernoulli-finite-cost
kind: claim
title: Gamma_mal has fixed price iff its Bernoulli shift has finite cost, iff the single-stage floor fails, iff some free action weakly contained in Bernoulli has finite cost
distinct_from:
  fpbs-shifted-stage-relative-cost-zero-or-infinite: that gives C(beta) = 2 iff relC over H_1 is 0; this adds that C(beta) = 2 already forces every free action of Gamma_mal to have cost 2, which needs monotonicity of cost under weak containment.
  fpbs-mal-bernoulli-single-stage-floor: that is the open floor; this shows the floor is equivalent to Gamma_mal failing fixed price, in both directions.
  fpbs-mal-odometer-product-actions-have-cost-two: that proves the floor would give a counterexample; this proves the converse, that failure of the floor gives fixed price.
  fpbs-locally-free-free-actions-have-finite-cost: that is the statement for all locally free groups; this is the equivalence for Gamma_mal alone, together with the weak-containment relaxation.
artifacts:
  - research/artifacts/fpbs-finite-cost-transfers-up-weak-containment-2026-09-18.md
---

**ESTABLISHED** through `fpbs-mal-fixed-price-iff-bernoulli-finite-cost-proof`.

Let `Gamma_mal = <a, b_1, b_2, ... | b_k = b_{k+1} a b_{k+1}^{-2}>`, with
`H_1 = <a, b_1>` and `β` its Bernoulli shift. The following are equivalent:

1. `Gamma_mal` has fixed price;
2. `C(β) < ∞`;
3. `C(β) = 2`;
4. `relC(E_β; E_{β|H_1}) = 0`;
5. some free action `a` with `a ≼ β` has finite cost, for instance a free
   factor of `β` or a free factor of iid;
6. `fpbs-mal-bernoulli-single-stage-floor` fails.

When they hold, every free action of `Gamma_mal` has cost 2.

**Consequence.** `fpbs-mal-bernoulli-single-stage-floor` holds iff `Gamma_mal`
is a counterexample to `fpbs-fixed-price-universal`. The fixed-price question
for `Gamma_mal` is therefore exactly one Bernoulli statement.

Item 5 is a relaxation for attacks on the negation. It suffices to find any
free action of finite cost that is weakly contained in `β`, with no
invariance or mixing required. Actions with a compact abelian factor, such as
the odometer products, are excluded from item 5. Their Koopman representation
has a finite-dimensional piece, which cannot be weakly contained in the
regular representation of the non-amenable `Gamma_mal`.

Artifact: `research/artifacts/fpbs-finite-cost-transfers-up-weak-containment-2026-09-18.md`, §4, Corollary 4.
