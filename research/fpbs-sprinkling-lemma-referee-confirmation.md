---
rg: 2
id: fpbs-sprinkling-lemma-referee-confirmation
kind: claim
title: The one-edge sprinkling l2 Lipschitz proof survives a referee pass of its own, with the strictness step in item 3 derived from item 2
distinct_from:
  fpbs-one-edge-sprinkling-l2-lipschitz: that is the sprinkling lemma itself; this is the referee gap that keeps its proof route from deriving it, left open because the lemma was refuted in a batch with a separate claim.
  fpbs-uniform-floor-equivalence-restricted-to-monotone-paths: that repairs the refuted floor-endpoint equivalence; this asks for no new mathematics, only a separate referee pass and one corrected justification.
  fpbs-gap-survives-product-generator-moves: that compares thresholds under generator moves through the margin m(S); this is a verification gap in one proof route.
---

**OPEN.** On 2026-09-17 all three referees voted refuted on a batch landing.
The batch paired `fpbs-one-edge-sprinkling-l2-lipschitz` with
`fpbs-weighted-surface-continuity-reduces-to-uniform-floor`, and every
refutation targeted the second claim. All three referees checked the sprinkling
lemma and found it correct:
* the coupling `omega' = omega OR xi`;
* the split at the last omega-closed edge, which gives disjoint witnesses;
* BK on a finite product space, then exhaustion by monotone convergence;
* the Lipschitz constant `deg_max/eps`;
* the fresh-generator identity `R = p A_{S''}`.

**Claim.** The route `fpbs-one-edge-sprinkling-l2-lipschitz-proof` passes a
referee pass that covers only that claim. In that route, item 3's strict
inequality `p < p_{2->2}` is derived from the openness in item 2, not "by
definition", as one referee noted.

Once such a pass is recorded, drop this requirement from
`fpbs-one-edge-sprinkling-l2-lipschitz-proof`.

## Attempts

1. **Batch referee pass, 2026-09-17.** Three lenses checked the lemma inside a
   batch vote and found each step correct. **Where it stops:** the vote was
   cast on the batch, which was refuted because of the floor-endpoint
   equivalence in a different claim. A per-claim vote has not been recorded.
