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

Exhaust Gamma by finitely generated subgroups Gamma_n. Under the hypothesis,
the restriction to Gamma_n has an action-independent cost c_n. Its orbit
relations exhaust the full action relation, so the definition of pseudocost
gives only the shared upper bound

    PC(R_alpha) <= liminf_n c_n.

It does not show equality with this particular bound, or equality between
the pseudocosts of two actions. This remains a gap even if cost and pseudocost
are assumed equal. For the cost-one case, the increasing-union argument is
already used in `fpbs-amen2-case-split-countable-exhaustion-proof`.

**Source correction, September 10, 2026.** In
[Tucker-Drob, arXiv:1211.6395](https://arxiv.org/pdf/1211.6395), Proposition
6.7 gives the exhaustion inequalities, and Corollary 6.8 gives C=PC for
finite-cost or treeable relations, as well as PC=1 iff C=1. Corollary 6.5,
previously cited here, instead concerns upper semicontinuity for finitely
generated groups. Question 7.6 asks whether PC<C can occur at all; the earlier
wording must not be read as asserting a known strict example. No source
checked supplies the universal passage claimed by this node.
