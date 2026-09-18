---
rg: 2
id: fpbs-normal-finite-cost-rankgradient-counterexample-reduction
kind: claim
title: A positive-gradient normal chain in a group with a finite-cost normal subgroup of infinite index would refute fixed price
distinct_from:
  fpbs-kazhdan-rankgradient-counterexample-reduction: that takes the cheap action from Hutchcroft-Pete and needs property (T); this takes it from Gaboriau's finite-cost normal subgroup theorem and needs no rigidity, only an infinite normal subgroup of infinite index and finite infimal cost.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that asserts fixed price one for such extensions; this is the conditional refutation of fixed price if a positive-gradient chain exists, i.e. the negation of a consequence of that claim.
artifacts:
  - research/artifacts/fpbs/normal-finite-cost-rank-gradient-2026-09-17.md
---

**Theorem R.** Assume:

* `G` is finitely generated;
* `N` is an infinite normal subgroup of infinite index with `cost(N) < ∞`;
* `(G_n)` is a descending chain of finite-index normal subgroups with trivial intersection and `RG(G,(G_n)) > 0`.

Then `G` has free p.m.p. actions of cost arbitrarily close to one, and a free profinite action of cost `1 + RG(G,(G_n)) > 1`. So `G` does not have fixed price.

Section 1 of the linked note gives the proof. The theorem is conditional: no example is supplied. Section 5 of the same note shows that such an example must either make `N` itself a counterexample, or use a chain with `[G:G_nN]` bounded (claim `fpbs-bounded-cost-normal-unbounded-chain-zero-rank-gradient`).
