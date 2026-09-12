---
rg: 2
id: infranormal-compact-closure-normal
kind: claim
title: Infranormal subgroups have normal closure in every compact image
invalidates: [compact-bogoliubov-clifford-model]
distinct_from:
  finite-infranormal-subgroup-is-normal: This theorem concerns the closure of an arbitrary infranormal subgroup after mapping the ambient group into a compact group; the other uses finiteness of the subgroup itself to identify its compression semigroup with its normalizer.
artifacts:
  - notes/FALSE_COMPACT_BOGOLIUBOV_APPROXIMATION_FOR_KUN_THOM.md
---

If `P_Gamma={g : g Gamma g^(-1)<=Gamma}` generates `G`, then for every
homomorphism `rho:G->K` to a compact group, the closure of `rho(Gamma)` is
normal in the closure of `rho(G)`.  Compact recurrence upgrades each
one-sided inclusion to equality.  Consequently the `Gamma`-fixed space of
every finite-dimensional unitary representation is `G`-invariant.
