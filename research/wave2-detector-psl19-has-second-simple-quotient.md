---
rg: 2
id: wave2-detector-psl19-has-second-simple-quotient
kind: claim
title: The explicit PSL2(19) triangle maps onto PSL2(19) squared, so its perfect first kernel has a nontrivial simple quotient
distinct_from:
  wave2-detector-psl19-no-solvable-refinements: that excludes solvable-kernel refinements of the canonical quotient; this constructs an actual nonsolvable-kernel refinement, marking the exact limitation
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-detectors-2026-09-20.md
  - experiments/hrf-wave2-detectors-2026-09-20/psl19_quotient_census.py
  - experiments/hrf-wave2-detectors-2026-09-20/psl19_quotient_census_result.json
---

For the explicit triangle `Λ` and canonical quotient `f_0:Λ -> Q`
in [[wave2-detector-psl19-perfect-first-kernel]], there is a second
quotient `f_1:Λ -> Q` such that `(f_0,f_1):Λ -> Q×Q` is surjective.
Consequently its perfect first kernel `N=ker f_0` surjects onto `Q`.

The second map is identity on vertex1 and conjugation `g -> u^-1 g u`
and `g -> v^-1 g v` on vertices2 and3, respectively, where the elements
of `PGL_2(19)` are

```
u = [[1,5],[9,17]],   v = [[1,14],[12,13]].
```

This provides a concrete nonsolvable next quotient, not a central-twist
detector: `Q×Q` has zero degree-two cohomology with `F_5` coefficients.
The kernel of this product quotient has not had its integral homology
computed here. No claim that it is perfect is made.

**Status:** independently reviewed exact matrix certificate and written
group-theoretic argument; the census was independently rerun on 2026-09-20.
See `research/artifacts/hyperbolic-rf-wave2-audit-2026-09-20.md`.

Proof: [[wave2-detector-psl19-second-simple-quotient-proof]].
