---
rg: 2
id: wave4-h31-first-product-kernel-is-perfect
kind: claim
title: The kernel of the canonical H31 quotient to PSL2(31) times C5 is perfect
distinct_from:
  h31-seven-central-image-criterion: that gives the first retraction kernel's cohomology away from five; this computes its mod-five abelianization and proves that the next kernel is perfect.
  wave3-audit-h31-abelian-sylow-images: that classifies images with abelian Sylow-five subgroups; this excludes all solvable-kernel refinements of the specified product quotient.
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-h31-perfect-kernel-2026-09-20.md
  - experiments/hrf-wave4-h31-2026-09-20/retraction_module.py
  - experiments/hrf-wave4-h31-2026-09-20/retraction_module_result.json
---

Let H=H31 and Q=PSL2(31). The canonical retraction kernel K=ker(H->Q)
has abelianization C5. The kernel N of H->Q x C5, sending c to the
second factor, is perfect. Hence every finite quotient of H whose image
of N is solvable factors through Q x C5. This excludes all nontrivial
solvable-kernel refinements of this specified quotient.

The orbit complex N\X is the union of five cones on the connected
bipartite coset graph of Q/<a> and Q/<b>. For ell!=5 its second homology
with Fell coefficients has dimension35716 and its first homology is zero.
No restriction on arbitrary nonsolvable refinements is asserted.
