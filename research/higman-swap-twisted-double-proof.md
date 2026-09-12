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
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
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

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently.
- `psi` restricts to `theta`, which gives the transport.
- `alpha` permutes the relators.
- The eliminated relators are `t`-conjugates of the remaining ones.
- The commensurability step holds via the `A^n` alphabet.
- Scope note: the sign character kills `(1+g)/2` for every involution `g = ht`, because `chi|_H` is trivial and `H` is torsion-free. So the corner conclusion covers every finite subgroup of `E`, not only `<t>`.
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 25.)
