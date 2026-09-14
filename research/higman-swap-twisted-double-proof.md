---
rg: 2
id: higman-swap-twisted-double-proof
kind: route
title: Transport the second Baumslag--Solitar amalgam along the relabelling isomorphism and eliminate generators
target: higman-group-is-the-swap-twisted-double-of-a-bs-amalgam
requires:
  - higman-group-splits-as-amalgams-over-free-subgroups
  - surjunctivity-is-a-commensurability-invariant
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

## Why sufficient

Artifact Section 4, Theorem 4.1.

* `psi : a -> c, b -> d, c -> a` is an isomorphism `<a,b,c> -> <c,d,a>` that restricts to the swap on `<a,c>`.
  Transporting the splitting `H = <a,b,c> *_<a,c> <c,d,a>` back along `psi` gives the twisted double.
* `alpha` permutes the four relators and squares to the identity. In `H x|_alpha Z/2`, eliminating `c = tat` and
  `d = tbt` leaves `t^2`, `b^a = b^2` and `(tat)^b = (tat)^2`, because the other two Higman relators are
  `t`-conjugates of these. The same presentation defines `G_1 *_F (F x|_theta Z/2)`.
* `H` has index two in `E`, so `surjunctivity-is-a-commensurability-invariant` gives the equivalence.
* The sign character `t -> -1`, `a, b -> 1` respects the relators, and it or the trivial character sends each of
  `(1 +- t)/2` to 0, so `c e b = 1` maps to `0 = 1`.
