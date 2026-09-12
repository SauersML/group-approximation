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
  Atiyah conjecture;
- over every field, every subgroup of a torsion-free virtually compact special
  group or of a compact 3-manifold group
  (`fisher-sanchez-peralta-special-and-3-manifold-domains`, consequence
  `zero-divisor-host-is-not-virtually-compact-special`).

The unit conjecture is false over `F_2` (Gardam) and also over `C`
(`unit-conjecture-fails-over-complex-numbers`, Gardam arXiv:2312.05240), both on
the Promislow group. That group is elementary amenable, so it satisfies this
conjecture.

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
  - **Fournier-Facio's torsion-free nonsofic group.** It is built from a
    universal finitely presented torsion-free group `U <= P`
    (`fournier-facio-torsion-free-skeleton`). The final quotient `pi` is
    controlled only on a finite set; it is injective on `S` by simplicity.
    Whether `U` survives in `G`, and whether `G` has solvable word problem,
    is not established (checked against arXiv:2608.02025 §2 by the
    `nh-fournier-facio` lane). The construction is existential and gives no
    explicit presentation, so exact Cayley balls are not available.
  - **Characteristic-zero actors.** The torsion-free finite-index subgroups of
    `char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup` have
    exact multiplication and are admissible hosts. They are residually
    finite, hence sofic, so they are not tied to nonsoficity.
  - **`E_3(3)` in `SL_3(Z)`.** The explicit admissible host with exact
    multiplication is a torsion-free finite-index subgroup of `SL_3(Z)`, the
    characteristic-zero actor factor:
    `E_3(3) = <e_ij(3) : i != j>`. It lies in the principal congruence
    subgroup `Gamma(3)`, hence is torsion-free by Minkowski. It has property
    (T), is not elementary amenable, and is not left-orderable (Witte, Proc.
    AMS 122 (1994)). Unique products are not known for it here. A
    Gardam-style SAT census on its balls is in `experiments/zero-divisor-tf/`.
  - **Field-independent census on `E_3(3)`.** A zero divisor over any field
    needs a support pair without a uniquely represented product. SAT excludes
    such pairs with radii `(2,2)` and `(2,3)` in either order
    (`e33-no-unique-product-pairs-of-small-radius`). So no zero divisor over
    any field has supports of these radii. The `(3,3)` and `(2,4)` instances
    were still running on MSI when this bullet landed; outputs go to
    `/projects/standard/hsiehph/sauer354/zero-divisor-tf/runs-up/`.
