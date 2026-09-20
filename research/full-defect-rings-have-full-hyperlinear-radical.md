---
rg: 2
id: full-defect-rings-have-full-hyperlinear-radical
kind: claim
title: "Full complementary idempotents force trivial hyperlinear images of every elementary rank at least two"
distinct_from:
  full-defect-ring-non-mf-at-rank-two: "That has the same ring and rank scope for MF targets; this concludes triviality for all hyperlinear targets using the new analytic normalization input."
  cohn-rank-four-has-full-hyperlinear-radical: "That is the universal finitely generated Kazhdan source; this transfers its annihilation to arbitrary countable full-defect rings and rank two."
artifacts:
  - research/artifacts/full-defect-ring-hyperlinear-radical-audit-2026-09-20.md
---

Let R be a countable nonzero unital associative ring with s,t in R
such that ts=1 and R(1-st)R=R. For every integer n>=2, every
homomorphism EL_n(R)->K to a hyperlinear group is trivial. Equivalently,
every homomorphism from EL_n(R) into every tracial matrix ultraproduct
is trivial, and Rad_hyp(EL_n(R))=EL_n(R).

No finite generation of R, characteristic restriction, or property (T)
of EL_2(R) is required. The full defect supplies two half-orthogonal
copies, not a decomposition exhausting 1. As a consequence R^x is
nonhyperlinear, since it contains an embedded EL_4(R); this does not
assert that every homomorphism from the entire unit group is trivial.

## Attribution

The new analytic input is Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorems 1.2/6.7 and 1.3/7.4, and Andreas Thom's
conditional internality-to-normalization implication. The full-defect
ring theorem and rank-two normal-generation transfer for MF targets
are earlier Cairn/OpenAI manuscript algebra. This is their conditional
hyperlinear upgrade, not a ring theorem claimed to appear in Liu's paper.

## Attempts

2026-09-20: independently checked the universal Cohn calculation,
fullness-to-two-copies formulas, corner transfer, and rank-two normal
generator in the cited audit. All nontrivial analytic dependence stays
in the universal Cohn prerequisite. The older Clifford marked-word
countermodel is not contradicted; no generic MF-to-hyperlinear transfer
is asserted.
