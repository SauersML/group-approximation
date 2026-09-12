---
rg: 2
id: deligne-universal-cover-lattice-is-non-rf-kazhdan
kind: claim
title: The preimage of Sp_2n(Z) in the universal cover of Sp_2n(R) is a Kazhdan group that is not residually finite
distinct_from:
  dogon-sp2g-weak-ucp-nonhyperlinear: that makes this lattice non-hyperlinear under a weak ucp-stability hypothesis; this imports only property (T), finite presentation of the base and Deligne's failure of residual finiteness, with no hypothesis.
  deligne-triple-cover-finite-residual-is-center: that computes the finite residual of the triple cover of Sp4(Z); this is the infinite cyclic central extension given by the universal cover.
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that asks for a non-residually-finite Kazhdan group whose full C*-algebra has the local lifting property; this records one non-residually-finite Kazhdan group and makes no operator-algebra claim.
---

**ESTABLISHED by citation.** Let `n >= 2`, let `G = Sp_2n(R)`, let
`p: G~ -> G` be the universal covering, and let `Gamma = Sp_2n(Z)` and
`Gamma~ = p^-1(Gamma)`.

1. `ker p = pi_1(G) = Z` is a discrete central subgroup of `G~`, so
   `1 -> Z -> Gamma~ -> Gamma -> 1` is a central extension.
2. `Gamma` is an arithmetic lattice in `G`, so it is finitely presented.
3. `Gamma~` is a lattice in `G~` and has property (T).
4. `Gamma~` is not residually finite (Deligne).

The sources are in `deligne-universal-cover-lattice-is-non-rf-kazhdan-citation`.
The consumer is `deligne-lattice-embeds-in-no-rover-nekrashevych-group`.
