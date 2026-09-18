---
rg: 2
id: lifted-thompson-t-center-has-relative-t
kind: claim
title: "The pair (T-bar, Z) has relative property (T): every cnd function on the lift T-bar of Thompson's T is bounded on its centre"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that asks relative (T) for (C(C,Z) ⋊ V, Z·1_C); this is the same statement for the subgroup T-bar, whose centre goes to Z·1_C. It is stronger and implies that claim.
  lifted-thompson-t-is-a-t-menable: that is the Haagerup property of T-bar; this claim refutes it
refuted_by:
  - lifted-thompson-t-is-a-t-menable
---

**Statement.** Let `T̄` be the lift of Thompson's `T` to `R`, and let `z(x) = x + 1`. For every
cnd function `ψ` on `T̄`, `sup_M ψ(z^M) < ∞`.

**Status.** OPEN.

**Why it matters.** It is a one-dimensional sufficient condition for refuting
`brin-thompson-groups-nv-are-a-t-menable`:
- it implies `cantor-integer-maps-central-direction-has-relative-t`, through
  `cantor-integer-maps-central-direction-via-lifted-thompson-t`;
- that implies `cantor-integer-maps-by-v-are-not-a-t-menable`, and hence that `2V` is not
  Haagerup.

**Evidence either way.**
- The class of the extension is bounded, since the rotation number gives `rot(z) = 1`.
- On the refuting side: bounded-class central extensions *can* have a relatively-(T) centre, as
  in lifts of lattices of `Sp(2n,R)`, but there the quotient has (T). No example with a
  Haagerup quotient is known to this lane. By arXiv:1905.10081, p. 96, the question whether
  Haagerup lifts through central extensions is open.
- On the supporting side: lattices in the universal cover of `SL_2(R)`, and the braid group
  `B_3`, which is the lift of `PSL_2(Z) ≤ T`, are Haagerup. There the centre is not relatively
  (T).
- A proof would need an invariant that sees the centre through cnd functions. Quasimorphisms do
  not qualify, since they are not cnd.

## Attempts

None yet. The ruled-out witness classes are listed under `lifted-thompson-t-is-a-t-menable`,
Attempts 2026-09-18: permutation representations on dyadic orbits, and virtual splittings.
