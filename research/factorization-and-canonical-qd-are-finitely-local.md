---
rg: 2
id: factorization-and-canonical-qd-are-finitely-local
kind: claim
title: Group factorization and quasidiagonality of the full canonical trace are finitely local
distinct_from:
  stw99-problem-x1-fails-on-full-group-algebras: that asks for one factorization-property group whose canonical trace is not QD; this says both clauses can be tested on all finitely generated subgroups.
  literal-group-factorization-property: that is the now-established factorization claim for one finitely presented group; finite locality alone did not decide it.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

For a discrete group `G`, the following are finitely local properties:

1. `G` has Kirchberg's factorization property if and only if every finitely
   generated subgroup of `G` has the factorization property.
2. The canonical trace on `C*(G)` is quasidiagonal if and only if its
   restriction to `C*(H)` is quasidiagonal for every finitely generated
   subgroup `H<=G`.

Thus any full-group-algebra counterexample to STW Problem X(1) already has a
finitely generated subgroup whose canonical full-group trace is amenable but
not quasidiagonal.
