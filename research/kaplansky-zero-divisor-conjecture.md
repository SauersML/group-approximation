---
rg: 2
id: kaplansky-zero-divisor-conjecture
kind: claim
title: Group rings of torsion-free groups over fields have no zero divisors (Kaplansky)
root: true
distinct_from:
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that reduces the group quantifier to one fixed finitely presented torsion-free group; this is the conjecture itself.
  kaplansky-all-fields-reduce-to-finite-fields-on-one-group: that reduces every field to the finite fields on the fixed tester; this is the conjecture being reduced.
  strong-atiyah-torsion-free: that is the L^2-integrality conjecture, which implies this statement only in characteristic zero; this is the ring-theoretic statement over every field.
  algebraic-strong-atiyah-for-all-torsion-free-groups: that gives the characteristic-zero case over Qbar; this covers every field, including positive characteristic.
---

For every field `k` and every torsion-free group `G`, the group ring `k[G]`
has no zero divisors: `alpha beta = 0` in `k[G]` forces `alpha = 0` or
`beta = 0`.

*Marked `root` because it answers a top-level question in its own right*
(Kaplansky's zero-divisor conjecture).

Known cases:
- unique-product groups, over every field;
- torsion-free elementary amenable groups, over every division ring
  (Kropholler--Linnell--Moody);
- in characteristic zero, every torsion-free group satisfying the Strong
  Atiyah conjecture.

The unit conjecture over `F_2` is false (Gardam, on the Promislow group), but
that group is elementary amenable, so it satisfies this conjecture.

By `kaplansky-all-fields-reduce-to-finite-fields-on-one-group`, the conjecture
is equivalent to `F[U]` being a domain for every finite field `F` and one
fixed finitely presented torsion-free group `U`.

## Attempts

* **Fixed tester.** The route `zero-divisor-via-fixed-tester-finite-fields`
  needs `fixed-tester-finite-field-group-rings-are-domains`. It dies where the
  conjecture does: `U` contains every finitely presented torsion-free group,
  so no known method (unique products, elementary amenability, Atiyah)
  applies to it.
* **Counterexample hosts from this repository.** By
  `zero-divisor-support-subgroup-host-constraints`, the support subgroup must
  be finitely generated and torsion-free, must lack unique products, must not
  be elementary amenable, and in characteristic zero must violate Strong
  Atiyah. The candidates:
  - **Leavitt and Kun--Thom groups.** The binary Leavitt unit group and the
    Kun--Thom wreaths and doubles contain torsion. The Theorem E actors are
    not even virtually torsion-free
    (`kun-thom-actors-have-no-torsion-free-finite-index-subgroups`), so they
    give no host of finite index.
  - **Fournier-Facio's torsion-free nonsofic group.** It is glued from a
    universal finitely presented torsion-free group
    (`fournier-facio-torsion-free-skeleton`), so exact Cayley balls are not
    computable in general. Only certificates carrying explicit derivations of
    every cancellation, plus a separating quotient for nonvanishing, can be
    checked there.
  - **`E_3(3)` in `SL_3(Z)`.** The explicit admissible host with exact
    multiplication is a torsion-free finite-index subgroup of `SL_3(Z)`, the
    characteristic-zero actor factor:
    `E_3(3) = <e_ij(3) : i != j>`. It lies in the principal congruence
    subgroup `Gamma(3)`, hence is torsion-free by Minkowski. It has property
    (T), is not elementary amenable, and is not left-orderable (Witte, Proc.
    AMS 122 (1994)). Unique products are not known for it here. A
    Gardam-style SAT census on its balls is in `experiments/zero-divisor-tf/`.
