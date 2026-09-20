---
rg: 2
id: fpbs-cost-betti-fg-iff-fp-and-length-canonical-cost-lsc
kind: claim
title: Cost-Betti for all finitely generated groups plus beta_1 continuity along length-canonical covers is equivalent to cost-Betti for finitely presented groups plus cost lower semicontinuity along those covers
distinct_from:
  fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers: that shows semicontinuity fails along arbitrary finitely presented covers; this proves the reduction goes through along the enumeration-free length-canonical covers, given one explicit open input
  fpbs-fixed-price-countable-from-finitely-generated: that passes from finitely generated to countable groups; this passes from finitely presented to finitely generated groups
  fpbs-graphing-cost-betti-cycle-dimension-identity: that converts cost-Betti into cycle-tail compactness for one group; this reduces cost-Betti for a group to its finitely presented length-canonical covers
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

**ESTABLISHED.** For a marked group `G = F/N`, put `G^_R = F/<<N cap B_R>>`. This is finitely presented, and
`G^_R -> G`. Define the following statements.

- `T_fp`: `C(b_G) = 1 + beta_1(G)` for every infinite finitely presented `G`.
- `SEL_len(G)`: `C(b_G) <= liminf C(b_(G^_R))`.
- `BA_len(G)`: `beta_1(G^_R) -> beta_1(G)`.
- `CB`: `C(b_G) = 1 + beta_1(G)` for every infinite finitely generated `G`.

Then:

1. `T_fp` and `SEL_len` (for all `G`) together imply `CB`.
2. `CB` implies that `SEL_len(G)` and `BA_len(G)` are equivalent.
3. Hence `CB` and `BA_len` together are equivalent to `T_fp` and `SEL_len` together.

The proof of (1) is one line:

    C(b_G) <= liminf C(b_(G^_R)) = 1 + liminf beta_1(G^_R) <= 1 + beta_1(G),

using Pichot for the last step and the Gaboriau lower bound for the reverse inequality.

The three open inputs (`fpbs-cost-betti-for-finitely-presented-groups`,
`fpbs-bernoulli-cost-lsc-along-length-canonical-covers` and `fpbs-l2-betti-continuous-along-length-canonical-covers`)
can each fail on their own. Their arbitrary-cover analogues are false, by `fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers`.
Artifact, Section 3.
