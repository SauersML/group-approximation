---
rg: 2
id: finite-npa-portfolio-from-relaxation-monotonicity
kind: route
title: Bound every finite dictionary below by a standard level and quote one non-exact level
target: finite-npa-dictionary-portfolio-cannot-be-exact
requires:
  - chaturvedi-no-finite-npa-level-exact-in-2-2-2
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

Let `k` be the largest word length occurring in any `S_i`.  Each `S_i` is then
contained in the standard level-`k` dictionary, and restricting a feasible
level-`k` moment matrix to the principal submatrix indexed by `S_i` leaves a
positive semidefinite matrix satisfying every constraint `S_i` imposes.  Hence

```text
Q_k  is contained in  Q_(S_i)   for every i.
```

The prerequisite supplies a behaviour `p` in `Q_k \ Q`.  That single `p` lies in
every `Q_(S_i)`, hence in their intersection, and not in `Q`.

Note the argument does not need the union `S = union S_i` that the source
dossier formed: containment in one standard level already dominates every member
of the portfolio simultaneously, and it is what makes the adaptive-tree version
immediate as well -- a tree with finitely many reachable dictionaries has a
finite maximum word length.

The route is deliberately thin.  Its content is that the portfolio question
reduces to the single-level question with no loss, so nothing beyond the
imported theorem is being claimed.
