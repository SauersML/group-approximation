---
rg: 2
id: compression-wreath-not-finitely-presented
kind: claim
title: The compression wreath witnesses are never finitely presented
distinct_from:
  finitely-presented-sofic-non-mf: That established claim gives a finitely presented sofic non-MF group, namely the literal forty-one-relator `E`; this is the complementary negative fact that the *wreath* witnesses `K^(G/Gamma) x| G` can never be that group, so the finitely presented endpoint has to come from the presented construction and not from this family.
  torsion-free-finitely-presented-non-mf: That is a positive existence statement reached through the normal-Kazhdan defect route; this is a negative presentation-theoretic fact about the compression wreath products.
artifacts:
  - GroupApproximation/Sofic/AscendingHNNDoubleCosets.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

For every nontrivial finite `K`, the group

    W_K = K^(G*/Gamma*) x| G*

is finitely generated — at most `7 + d(K)` generators, so eight for `K = C2`
and nine for `K = A_5` — but is **not finitely presented**.  Neither is any of
its finite-index subgroups, and `W_K` is not abstractly commensurable with any
finitely presented group.

The obstruction is exact and structural rather than incidental: diagonal
orbits of `G*` on `(G*/Gamma*)^2` are the double cosets
`Gamma* \ G* / Gamma*`, and the HNN height homomorphism separates
`Gamma* t^n Gamma*` for distinct `n`, so there are infinitely many.  A finite
presentation of a transitive permutational wreath product with finitely
generated point stabilizer can only enforce finitely many orbits' worth of
cross-site commutators.
