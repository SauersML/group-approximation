---
rg: 2
id: higman-group-amalgam-splittings-proof
kind: route
title: Normal forms in the two Baumslag--Solitar amalgams give free amalgamated subgroups and both splittings
target: higman-group-splits-as-amalgams-over-free-subgroups
requires: []
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

## Why sufficient

Artifact Section 1, Theorem 1.1.

* `G_1` is presented as the union of the presentations of `BS(a,b)` and `BS(b,c)` with `b` identified, and
  `b` has infinite order in both, so `G_1 = BS(a,b) *_<b> BS(b,c)`.
* In `BS(a,b)` the quotient to `Z` sends `a` to 1 and `b` to 0, so `a^k in <b>` forces `k = 0`. In
  `BS(b,c)` it sends `b` to 1 and `c` to 0, so `c^l = b^m` forces `m = 0` and then `l = 0`.
* A nontrivial reduced word in `a, c` alternates nonzero powers of `a` and `c`, which lie in different
  factors outside the amalgamated subgroup, so it is nontrivial. The same holds in `G_2`, where `c` is a
  stable letter and `a` a base letter.
* The amalgam `G_1 *_(F_ac) G_2` has exactly the presentation of `H`. The cyclic relabelling
  `a -> b -> c -> d -> a` preserves the relators and gives the second splitting.

**Literature input, not a Cairn node:** amalgams of sofic groups over amenable subgroups are sofic
(Elek--Szabo, as cited by `amenable-envelope-magnus-piece-sofic-proof`; not re-read by this lane). It is
used only for the soficity bullet.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently.
- The stable and base roles in `B(a,b)`, `B(b,c)`, `B(c,d)` and `B(d,a)` hold, via the quotients to `Z`.
- Alternating powers are nontrivial by the normal form.
- `F_ac` is free on `{a,c}` in both factors, so the identification is an isomorphism.
- The union presentation is `H`'s, and the relabelling permutes the relators.
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 23.)
