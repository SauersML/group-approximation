---
rg: 2
id: kazhdan-compression-pairs-normalize-all-tracial-models
kind: claim
title: "Every tracial-ultraproduct model of a Kazhdan compression pair normalizes its subgroup commutant"
distinct_from:
  kt-centralizer-normalization-hs: "That is formulated for trace-preserving hyperlinear representations; this includes every homomorphism, which the finitary and CE countermodel consumers need."
artifacts:
  - research/artifacts/liu-section-six-acceptance-and-thom-bypass-2026-09-20.md
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorems 6.7 and 7.4. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn. Andreas Thom has priority for the conditional implication from the universal centralizer theorem to normalization; Liu explicitly credits it.

Let Gamma<=G be finitely generated Kazhdan groups and G=<Gamma,t_1,...,t_s> with t_i Gamma t_i^(-1)<=Gamma. For every homomorphism sigma:G->U(M) into any specified tracial matrix ultraproduct,
```
sigma(G) normalizes sigma(Gamma)' cap M.
```
No canonical-trace or injectivity condition is imposed. This is the universal-trace strengthening needed for finitary compression inequalities and to rule out nonnormalized commutants in Connes-embeddable models. Merely knowing the single binary wreath is nonhyperlinear would not give this conclusion.

## Attempts

2026-09-20: established through `all-trace-normalization-via-thom-no-drift`, using the now accepted universal internality theorem of Jihao Liu and Andreas Thom's checked conditional no-drift argument. Thom's proof uses internality of both subgroup and ambient commutants. This bypasses Liu Section 7; the alternate route using its stronger single-model hypothesis remains visible and does not need to be accepted to prove this claim. No canonical-trace or injectivity restriction has been introduced.
