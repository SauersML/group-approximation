---
rg: 2
id: just-infinite-base-hnn-has-only-finite-torsion-quotients-proof
kind: route
title: A nontrivial coinvariant relation has finite index in a just-infinite base
target: just-infinite-base-hnn-has-only-finite-torsion-quotients
requires:
  - ascending-hnn-torsion-quotients-see-only-coinvariants
---

Notation of `ascending-hnn-torsion-quotients-see-only-coinvariants`: `M_m` is the
normal closure in `B` of `{ b^-1 phi^m(b) : b in B }`, and `B_{phi^m} = B/M_m`.

**Item 1.** Let `pi: Gamma -> Q` be onto a torsion group, and let `m` be the
order of `pi(t)`. By item 1 of the cited claim, `pi(B)` has index dividing `m`
in `Q` and is a quotient of `B_{phi^m}`. By hypothesis `phi^m != id`, so some
`b^-1 phi^m(b)` is nontrivial, `M_m != 1`, and, `B` being just-infinite,
`|B : M_m| < infinity`. So `B_{phi^m}` is finite, `pi(B)` is finite, and `Q` is
finite. If `phi` is not surjective, then no power of `phi` is surjective, so no
power is the identity, and the hypothesis holds.

**Item 2.** Let `Gamma` be finitely presented and `B` not finitely presented. If
no power of `phi` is the identity, item 1 applies. Otherwise `phi^m = id` for
some `m >= 1`. Then `phi` is an automorphism, and `t^-m b t^m = phi^m(b) = b`
for all `b in B`, so `t^m` centralizes `B`. The subgroup `< B, t^m >` is the
preimage of `mZ` under `Gamma -> Gamma/N ≅ Z` (notation of the cited proof,
where `N = B` since `phi` is onto), so it has index `m`. It is isomorphic to
`B x Z`: `B` is normal in it, `t^m` has infinite order modulo `B`, and the two
commute. A finite-index subgroup of a finitely presented group is finitely
presented, so `B x Z` is finitely presented. A retract of a finitely presented
group is finitely presented, and `B` is a retract of `B x Z`. So `B` is finitely
presented, a contradiction.
