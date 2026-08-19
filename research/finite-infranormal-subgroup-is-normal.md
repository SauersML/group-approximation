---
rg: 2
id: finite-infranormal-subgroup-is-normal
kind: claim
title: A finite infranormal subgroup is normal
invalidates: [finite-pauli-kun-thom-splice]
distinct_from:
  finite-normal-compression-obstruction: This is an elementary algebraic normalizer lemma for finite infranormal subgroups; the other claim is an operator-norm matrix-corona vanishing theorem for finite normal compression defects.
artifacts:
  - notes/HYPERLINEAR_CAIRN_PROGRESS_2026-08-14.md
---

Let `K<G` be finite and put
`P_K={g in G : gKg^(-1) <= K}`.  Then `P_K=N_G(K)`, because conjugation
preserves the finite cardinality of `K` and turns the inclusion into
equality.  Consequently, if `P_K` generates `G` (infranormality in the
Kun--Thom sense), then `N_G(K)=G` and `K` is normal.

In particular no finite subgroup can be both nonnormal and infranormal, so
a fixed finite Pauli packet cannot replace the infinite nonnormal Kazhdan
subgroup in the Kun--Thom sofic-radical theorem.
