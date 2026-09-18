---
rg: 2
id: fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation
kind: claim
title: Cost preservation along compact and along relatively weakly mixing extensions gives cost preservation along every free factor
distinct_from:
  fpbs-factor-invariance-equals-fixed-price: that identifies cost preservation along all free factors with fixed price; this reduces cost preservation along all free factors to the two Furstenberg-Zimmer classes of extensions, per group.
  fpbs-traffic-variational-cost-identities: that supplies variational formulas and continuity along increasing factors; this uses the continuity at the limit stages of a transfinite relative tower.
artifacts:
  - research/artifacts/fpbs-furstenberg-zimmer-cost-tower-2026-09-17.md
---

**ESTABLISHED.** Let G be a countably infinite group. Suppose that

* (P_c) every relatively compact extension V -> W of free p.m.p. G-actions with C(W) < infinity has C(V) = C(W), and
* (P_w) every relatively weakly mixing extension V -> W of free p.m.p. G-actions with C(W) < infinity has C(V) = C(W).

Then C(Y) = C(X) for every factor map Y -> X of free p.m.p. G-actions with C(X) < infinity. For finitely generated G the converse holds, so P_c and P_w together are equivalent to fixed price for G.

Proof (artifact Section 2). Start at B_X and recurse with the relative dichotomy of `relative-furstenberg-zimmer-dichotomy`. At a successor stage, a non-relatively-weakly-mixing step adds a strictly larger invariant sigma-algebra over which the stage is relatively compact. At limit stages take the generated sigma-algebra. The projections increase strictly in the separable space L²(Y), so the recursion stops at a countable ordinal beta, where Y is relatively weakly mixing over the stage. All stages are free because they factor onto X. By transfinite induction every stage has cost C(X). Successors use P_c. A countable limit uses a cofinal sequence and continuity along increasing factors, (10.1) of `fpbs-traffic-variational-cost-identities`. The last step uses P_w.

No ergodicity is assumed anywhere. The hypotheses concern arbitrary free bases, not only Bernoulli ones, since the intermediate stages are arbitrary. Neither P_c nor P_w is proved: see `fpbs-compact-extensions-preserve-cost` and `fpbs-relatively-weakly-mixing-extensions-preserve-cost`.

Status records a written deduction over imported theorems, not independent validation.
