---
rg: 2
id: fpbs-bernoulli-cost-lsc-along-length-canonical-covers
kind: claim
title: Bernoulli cost of a finitely generated group is the limit of the Bernoulli costs of its length-canonical finitely presented covers
distinct_from:
  fpbs-bernoulli-cost-usc-on-marked-groups: that proves the upper bound limsup <= along every convergent sequence; this is the lower bound, along the length-canonical covers only
  fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers: that shows the lower bound fails along arbitrary finitely presented covers; this asks for it along F/<<N cap B_R>>
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

**OPEN.** For every infinite finitely generated marked group `G = F/N`, with `G^_R = F/<<N cap B_R>>`,

    C(b_G) <= liminf_R C(b_(G^_R)).

By `fpbs-bernoulli-cost-usc-on-marked-groups`, this is equivalent to `C(b_(G^_R)) -> C(b_G)`. The statement does not
depend on an enumeration of relators.

The analogous statement for arbitrary finitely presented covers is false: `E_R -> (Z wr Z) * Z` has costs
`1 -> 2`. Along length-canonical covers that example does not jump.

Under `CB`, this statement is equivalent to `fpbs-l2-betti-continuous-along-length-canonical-covers`. Artifact,
Section 3.
