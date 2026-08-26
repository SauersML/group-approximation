---
rg: 2
id: sofic-recognition-two-generator-recursive-is-pi2-complete
kind: claim
title: Soficity is Pi-zero-two complete for two-generator recursive presentations and for subgroups of one finitely presented group
artifacts:
  - GroupApproximation/Computability/SoficRecognitionSecondLevel.lean
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
  - GroupApproximation/Endpoint/MainResults.lean
distinct_from:
  mf-recognition-two-generator-recursive-is-pi2-complete: that classifies MF and LEF with the sofic non-MF seed; this classifies soficity itself, which needs a nonsofic seed and the permutation upper bound, and neither theorem implies the other.
  finitely-presented-nonsofic-group-exists: that is the single existence input; this is the complexity classification it unlocks.
  mf-recognition-for-subgroups-of-one-fp-group-is-pi2-complete: that is the fixed-ambient theorem for MF; this is its sofic analogue, which is not among the properties between residual finiteness and MF that node covers.
---

ESTABLISHED, unconditionally.  For recursive presentations on two
generators and for pairs of words in Higman's universal finitely presented
group `V`,

```text
SOFIC_rec2                            is Pi^0_2-complete,
NONSOFIC_rec2                         is Sigma^0_2-complete,
{ (u_1,u_2) : <u_1,u_2> <= V sofic }  is Pi^0_2-complete.           (SC1)
```

The hardness map is `e |-> B2(S_e)` with the parametric switch seeded by a
finitely presented nonsofic group: `e in INF` gives the residually finite
group `B2(1)`, and `e in FIN` gives a group containing the nonsofic seed.

Consequently there is no algorithm that, given a two-generator recursive
presentation, decides soficity, and neither the sofic nor the nonsofic
presentations are recursively enumerable; the problem sits exactly at the
second level of the arithmetical hierarchy, alongside `INF` and `FIN`.

This is the first complexity classification of soficity.  It uses the
existence of a nonsofic group only through
[[finitely-presented-nonsofic-group-exists]], the cover lemma already being
built into that node; and it is optimal in the number of generators.
