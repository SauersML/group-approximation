---
rg: 2
id: fpbs-fixed-price-countable-from-finitely-generated
kind: claim
title: Fixed price for all finitely generated groups would give it for all countably infinite groups
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
---

**OPEN.** Assume every infinite finitely generated group has fixed price. Prove that every countably infinite group does. The original finite-routing arguments use finitely many generator demands. Section 9 of the conditional-traffic artifact now extends the variational identities to arbitrary countable groups when the base action has finite cost, by explicitly paying a generating graphing's unprocessed tail. It does not produce vanishing defect from the finitely generated Fixed Price hypothesis, or handle a finite-cost source over an infinite-cost base. No route establishes the passage.

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

The exhaustion bound can be arbitrarily loose even for known fixed-price
groups. Take Gamma_n=F_(4^n) x (Z/2Z)^n, nested by the free-factor and
coordinate inclusions. Their fixed prices are
1+(4^n-1)/2^n, which diverge, while their union is
F_infinity x direct-sum_N(Z/2Z), of fixed price one because it has an
infinite amenable normal subgroup. The finite-stage values follow by
finite-index scaling from the free factors. This is the explicit pattern
in [Gaboriau's lectures, Exercise 2.60(1)](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf),
not a new example. It rules out identifying cost with the liminf of the
costs of an arbitrary finitely generated subgroup exhaustion.

The extended traffic theorem identifies two remaining requirements for
the universal objective: obtain simultaneous near-optimal budget and
vanishing defect for every finite-cost base factor, and exclude finite-cost
extensions of infinite-cost free bases. The first would equate all finite
action costs via product projections. The second would exclude mixed
finite/infinite action costs. Neither follows here from the hypothesis
of this node, and neither is asserted proved.
