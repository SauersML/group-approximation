---
rg: 2
id: stw90-strict-comparison-failure-reflects-finitely
kind: claim
title: Failure of canonical strict comparison reflects to a finitely generated subgroup
distinct_from:
  stw99-problem-xc-cstar-simple-strict-comparison: this localizes any negative witness but does not ensure the reflecting finitely generated subgroup is C*-simple.
  stw90-directed-unions-of-strict-comparison-groups: that is the forward permanence theorem; this is its counterexample-facing finite reflection consequence.
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

If a discrete group `G` has the property that `C*_r(G)` fails strict
comparison with respect to its canonical trace, then there is a finitely
generated subgroup `H<=G` for which `C*_r(H)` also fails strict comparison
with respect to its canonical trace.

Thus every negative answer to STW Problem XC has a finitely generated local
comparison defect, although the subgroup carrying that defect need not itself
be C*-simple.  This last caveat prevents the statement from reducing XC to
the finitely generated C*-simple case.
