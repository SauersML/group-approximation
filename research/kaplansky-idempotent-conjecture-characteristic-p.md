---
rg: 2
id: kaplansky-idempotent-conjecture-characteristic-p
kind: claim
title: Group rings of torsion-free groups over fields of positive characteristic have no nontrivial idempotents
distinct_from:
  kaplansky-zero-divisor-conjecture: that is the domain conjecture over every field, which implies this; this is the weaker idempotent statement, restricted to positive characteristic.
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that reduces the group quantifier to one finitely presented tester; this is the conjecture itself in characteristic p.
  rank-one-lattice-kadison-kaplansky-and-charzero-idempotents: that settles the characteristic-zero idempotent statement for one class of lattices through Baum--Connes; this is the positive-characteristic statement, where no analytic tool applies.
---

For every prime `p`, every field `K` of characteristic `p` and every
torsion-free group `G`, the only idempotents of `K[G]` are `0` and `1`.

OPEN. This is Kaplansky's idempotent conjecture in positive characteristic.

## Known cases recorded on main

Every case below except the last two comes through the zero-divisor conjecture,
since `e(1-e) = 0`. The route is `modular-idempotents-via-zero-divisor-conjecture`.
- Unique-product groups, and torsion-free elementary amenable groups
  (Kropholler--Linnell--Moody): see `kaplansky-zero-divisor-conjecture`.
  This includes the Promislow group, so the unit counterexamples on that group
  (Gardam, Murray) have no idempotent analogue.
- Subgroups of torsion-free virtually compact special groups and of compact
  3-manifold groups, over every field (`fisher-sanchez-peralta-special-and-3-manifold-domains`).
- Subgroups of `p`-adic congruence kernels `CS(u,d,p)`, only in the same
  characteristic `p` (`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`).
- New, idempotent-specific: every residually finite `p`-group, torsion allowed
  (`residually-p-groups-have-trivial-idempotents-in-characteristic-p`).
- New: the class of groups with only trivial idempotents over `K` is closed
  under fully residual limits (`fully-residual-limits-preserve-trivial-idempotents`).

All fields reduce to finite fields on one fixed tester group
(`kaplansky-all-fields-reduce-to-finite-fields-on-one-group`).

## Attempts

1. **Promislow group through a matrix embedding.** Not needed: the group is
   elementary amenable and residually 2, so both Kropholler--Linnell--Moody and
   the residual-2 criterion already give trivial idempotents. See
   `research/artifacts/idempotent-charp-boundary-2026-09-13.md`.
2. **Finite quotients.** A finite group `Q` has only trivial idempotents over
   `K` exactly when `Q` is a `p`-group: if `g` has order `l` prime to `p`, then
   `(1/l)(1 + g + ... + g^(l-1))` is a nontrivial idempotent. So residual methods
   through finite quotients give exactly the residually-`p` class.
3. **Gap.** No listed mechanism covers torsion-free groups in characteristic
   `p` that:
   - lack unique products;
   - are neither elementary amenable nor virtually special;
   - do not lie in a `p`-adic congruence kernel for the same prime;
   - are not fully residually in the class above.

   Natural test groups are torsion-free Kazhdan lattices over primes other than
   their congruence primes, e.g. `Gamma(3) <= SL_3(Z)` over `F_2`. Main has no
   residual-2 or domain statement for that group.
