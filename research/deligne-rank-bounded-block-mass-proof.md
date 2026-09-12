---
rg: 2
id: deligne-rank-bounded-block-mass-proof
kind: route
title: Exactness on a presentation window yields a homomorphism separating z, and block defects add up
target: deligne-rank-models-carry-no-bounded-block-mass
requires:
  - deligne-triple-cover-finite-residual-is-center
  - finitely-generated-linear-groups-are-residually-finite
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Artifact Lemma 0.1 and Proposition 1.1.
1. **Window lemma.** Take the pairs met while evaluating the relators of a finite presentation of `E_3` letter by
   letter. Exactness on them defines a homomorphism `E_3 -> GL(W)` with `z -> w^j`. Its image is finitely
   generated linear, hence residually finite, so it gives a finite quotient separating `z`, against the finite
   residual.
2. **Blocks.** Defects of block-diagonal operators add over the blocks. By step 1 every block has defect at least
   one at some window pair.
3. **Count.** The blocks of dimension at most `m` number at most `|R_0| eps d`, so they carry at most
   `m |R_0| eps d` dimensions.
