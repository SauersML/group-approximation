---
rg: 2
id: fpbs-fixed-price-countable-from-finitely-generated
kind: claim
title: Fixed price for all finitely generated groups would give it for all countably infinite groups
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
---

**OPEN.** Assume every infinite finitely generated group has fixed price. Prove that every countably infinite group does. The finite-routing arguments behind the reuse programme use a finite generating set throughout: finitely many demands per root, finite path words, and bounded measurable traffic. The general countable formulation admits infinite generating sets and potentially infinite cost, and the source notes explicitly decline to extend their finitely generated conclusions to it. No route establishes the passage.

## Attempts

Exhaust by finitely generated subgroups. This is the standard move and it is already used in this graph for the cost-one case, where summable relative costs over an increasing union keep every stage at cost one (`fpbs-amen2-case-split-countable-exhaustion-proof`). For a common value above one there is no such telescoping: the relative costs of the successive stages need not sum to zero, so equality at each stage does not transfer to the union, and the cost of an increasing union is where cost and pseudocost part company (Tucker-Drob, arXiv:1211.6395, Section 6 and Corollary 6.5). The conditional-traffic and reuse notes both stop at the same boundary, in Section 8 and Section 7 respectively.
