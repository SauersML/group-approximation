---
rg: 2
id: mf-radical-functoriality-proof
kind: route
title: Pull corona representations back along group homomorphisms
target: mf-radical-functoriality
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/ManuscriptExactWrappers.lean
---

## Direct proof

If `x` lies in every corona kernel of `G` and `Theta` is any corona
representation of `H`, then `Theta o f` is a corona representation of `G`.
Hence `Theta(f(x)) = 1`; intersecting over `Theta` gives
`f(x) in Rad_MF(H)`.  If `H` is MF, a faithful corona representation of
`H` has trivial kernel, yielding the equivalent formulation.
