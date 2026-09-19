---
rg: 2
id: rich-2to1-conjecture-is-equivalent-to-ugc
kind: claim
title: The Rich 2-to-1 Games Conjecture is equivalent to the Unique Games Conjecture (Braverman--Khot--Minzer)
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED, BY CITATION.**  Braverman, Khot and Minzer,
*On Rich 2-to-1 Games*, ITCS 2021 (LIPIcs vol. 185, Article 27,
pp. 27:1--27:20, doi `10.4230/LIPIcs.ITCS.2021.27`), introduce the Rich
2-to-1 Games Conjecture and prove it **equivalent** to the Unique Games
Conjecture.  In their words: "We propose a variant of the 2-to-1 Games
Conjecture that we call the Rich 2-to-1 Games Conjecture and show that it
is equivalent to the Unique Games Conjecture."

Credit is theirs; nothing in this repository reproves it.  The equivalence
is what licenses the route `ugc-from-rich-2to1-via-bkm-equivalence` and,
read backwards, what stops the rich formulation from being mistaken for a
weaker target.

Context for why the rich variant is the useful side of the equivalence: the
2-to-1 Games Conjecture itself is a theorem, and the follow-up analytic
machinery -- Braverman, Khot, Lifshitz and Minzer, *An invariance principle
for the multi-slice, with applications*, Adv. Math. 480 (2025), Art. 110460,
arXiv:2110.10725 -- still states its perfect-completeness hardness
applications **conditionally on Rich 2-to-1**, rather than deriving richness
from the proved 2-to-1 hardness.  That conditionality is the gap the
`affine-orientation-glue-lemma` region attacks.
