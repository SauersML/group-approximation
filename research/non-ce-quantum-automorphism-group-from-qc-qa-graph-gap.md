---
rg: 2
id: non-ce-quantum-automorphism-group-from-qc-qa-graph-gap
kind: route
title: A qc-but-not-qa isomorphic graph pair gives a non-embeddable quantum automorphism group of its disjoint union
target: non-ce-quantum-automorphism-group-of-finite-graph-exists
requires:
  - qc-isomorphic-not-qa-isomorphic-graph-pair-exists
  - qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
---

Take a pair `(X, Y)` from `qc-isomorphic-not-qa-isomorphic-graph-pair-exists`.
Replace both graphs by their complements if `X` is disconnected; the
isomorphism algebra is unchanged.  Put `Z = X ⊔ Y`.

By `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group`, the central
projection `P = sum_(b in Y) u_(xb)` of `O(Qut Z)` has Haar trace `1/2`, and
`A(Iso(X,Y))` maps unitally into the corner `P O(Qut Z)`.  If
`L^infinity(Qut Z)` were Connes embeddable, the isomorphism game would have a
perfect `qa`-strategy.  So `Z` witnesses the target claim.
