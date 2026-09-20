---
rg: 2
id: wave2-ghb7-raw-supercentrality-does-not-reduce-stability
kind: claim
title: Scalar phase camouflage gives any hypothetical GHB7 instability witness arbitrarily strong relative centrality against its raw defect
distinct_from:
  wave2-ghb7-phase-normalized-defect-is-controlled-by-centrality: That compares centrality with defect after optimal phase removal; this proves why relative centrality measured against the raw defect cannot simplify the open rounding problem.
  hrf-audit-projective-internality-does-not-round: That constructs actual nonroundable projective models for other Kazhdan groups; this is a conditional transformation of any hypothetical GHB7 instability witness, with no existence assertion.
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-matching-2026-09-20.md
---

Fix k>0. If the GHB7 expanding-block rounding criterion fails, it has
a fixed-gap counterexample W_n with maximum plus-relator defect delta_n
and relator centrality error kappa_n satisfying

    kappa_n=o(delta_n^k).

It still has vanishing copy-equality defects and positive flexible
rounding-cost lower bound. Thus establishing rounding for all fixed-gap
sequences with this relative-centrality condition would already settle
the full expanding-block criterion; no weaker conjecture is isolated.

The proof multiplies both a copies of an alleged witness by exp(i t_n),
with t_n tending to zero more slowly than its original relator defects.
Scalar gap and centrality are unchanged, while the a^7 defect becomes
asymptotic to 7t_n. The perturbation tends to zero in operator norm,
so nonroundability persists. No GHB7 counterexample is asserted.

DERIVATION
wave2-ghb7-scalar-phase-camouflage-proof
