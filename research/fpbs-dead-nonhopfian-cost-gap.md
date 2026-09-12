---
rg: 2
id: fpbs-dead-nonhopfian-cost-gap
kind: route
title: Get two free actions of different cost from the non-Hopfian self-map
target: fpbs-fixed-price-counterexample-exists
requires:
  - fpbs-noninjective-pullback-action-is-free
artifacts:
  - research/artifacts/fpbs/torsionfree-local.md
  - research/artifacts/fpbs/responses/45_0909-153245.md
---

Dead: the attempt exploits the explicit surjective noninjective endomorphism a -> ab^100, b -> b of the torsion-free family, pulling a free action back along it and comparing the two costs, in the hope that the self-similarity separates them. The pullback is not essentially free, since the kernel acts trivially (fpbs-noninjective-pullback-is-not-free), so the pair it produces is not admissible for Fixed Price. Note also that the full-tail presentations are isomorphic as unmarked groups by an automorphism of the free group, which does not reverse the noninjectivity of the endomorphism.
