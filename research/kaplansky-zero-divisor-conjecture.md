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
  `zero-divisor-host-is-not-virtually-compact-special`);
- over fields of characteristic `0` or `p`, every subgroup of a `p`-adic
  congruence kernel `CS(u,d,p)` (Farkas--Linnell,
  `p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`). These include
  infinite Kazhdan groups such as `Gamma(3) <= SL_3(Z)`
  (`congruence-kazhdan-groups-satisfy-strong-atiyah`).

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
    *Correction (2026-09-12):* it is a host only in characteristics other
    than `0` and `3`, since `E_3(3) <= CS(1,3,3)` and Farkas--Linnell make
    its group ring a domain in characteristics `0` and `3`
    (`congruence-kazhdan-groups-satisfy-strong-atiyah`).
  - **Field-independent census on `E_3(3)`.** A zero divisor over any field
    needs a support pair without a uniquely represented product. SAT excludes
    such pairs with radii at most `(3,3)`, and with radii `(2,4)` or `(4,2)`
    (`e33-no-unique-product-pairs-of-small-radius`). So a zero divisor on
    this host, over any field, needs `rad_L(supp alpha) + rad_R(supp beta) >= 7`
    or one radius at least 5. The next instance, `(3,4)`, has about 9 million
    pairs; `(3,3)` already took 86 minutes of CaDiCaL.
  - **Known groups without unique products, sorted against the known cases.**
    Sources were read from the arXiv PDFs on 2026-09-12.
    - **Promislow and Nielsen--Soelberg groups: not hosts.** Promislow's group
      is virtually `Z^3`, and the two Nielsen--Soelberg groups are virtually
      class-2 nilpotent (Tabei, arXiv:2607.19687). All three are elementary
      amenable.
    - **Carter's groups `P_k`: not hosts.** They (arXiv:1302.0049, Theorem 2)
      are torsion-free, not amenable, and amalgams of two Klein bottle groups
      over `Z^2`. Carter shows that each satisfies this conjecture by Lewin's
      amalgam theorem. Each also has a finite-index subgroup `Z^2 x F` with
      `F` free, which is a right-angled Artin group, so `P_k` is virtually
      compact special as well.
    - **Generalised Rips--Segev groups: undecided.** These come from
      Rips--Segev 1987, Steenbock arXiv:1307.0981, Arzhantseva--Steenbock
      arXiv:1407.2441 (Theorem 1) and Gruber--Martin--Steenbock
      arXiv:1407.6850. They are torsion-free and hyperbolic, so not elementary
      amenable, and they would be excluded if cubulated (by Agol, then
      `zero-divisor-host-is-not-virtually-compact-special`). Martin--Steenbock
      (arXiv:1409.3678, §1.5) cubulate only classical `C'(1/6)` quotients of
      free products. They state that it is open whether these groups satisfy
      the conjecture, and ask whether some can be cubulated.
    - **Arzhantseva--Steenbock's Kazhdan groups: hosts, with one case open.**
      - They avoid the unique-product, elementary amenable, special and class-C
        cases (`kazhdan-groups-without-unique-products-are-zero-divisor-hosts`).
      - The Tarski monsters among them are not residually finite, so they also
        avoid linear groups and every `p`-adic congruence kernel, which is the
        Farkas--Linnell case above.
      - For the hyperbolic examples, the congruence case would force residual
        finiteness, and whether they are residually finite is open.

      These groups provably lack unique products. So the Tarski monsters are
      characteristic-0 hosts outside every case recorded above, which `E_3(3)`
      no longer is. No concrete presentation or normal form is recorded for
      them, so no ball census can run there.
    - **Bengi--Wise group: not classified here.** Bengi--Wise
      (arXiv:2602.11819) give a finitely generated, residually finite,
      torsion-free group all of whose finite-index subgroups contain
      Promislow's group.
* **Graphs of division rings (2026-09-17).** A zero-divisor host cannot be
  built from tree actions with known blocks.
  - **Loop-inclusive graph theorem.** The Fisher--Sanchez-Peralta graph-of-rings
    theorem is re-proved including the HNN case omitted in the source
    (`compatible-graphs-of-groups-with-loops-embed-in-division-rings`).
  - **Product-of-trees lattices.** Every torsion-free lattice in a product of two
    trees, and every graph of free groups, has `k[G]` inside a division ring over
    every field (`product-of-trees-lattices-embed-in-division-rings`). This is an
    instance of the source's graph corollary once the lattice is written as a graph
    of free groups, and it includes the finitely presented simple Burger--Mozes
    lattices. So `T x T` lattice censuses cannot produce hosts.
  - **Amenable edge groups.** Division-ring embeddability is closed under graphs
    of groups with amenable edge groups, whatever the vertex division rings
    (`amenable-edge-graphs-of-groups-preserve-division-ring-embeddings`). This
    gives a new class over every field, for example `Lambda *_Z P` with `Lambda`
    Burger--Mozes and `P` Promislow. It is not locally embeddable into
    unique-product, amenable or residually finite groups.
  - **What a host must do.** A host that splits over amenable subgroups needs a
    vertex group whose group ring embeds in no division ring.
  - **Amenability is sharp for arbitrary vertex rings (w3-059).** `k0[F2 x Z]`
    embeds epically in the Heisenberg Ore field with the `Z` factor sent into the
    closure of `F2`. The transversals of the non-amenable edge `F2` are then
    dependent, and the coproduct construction for `F2 x F2 = V *_F2 V` is not
    injective (`nonamenable-edges-break-division-ring-compatibility`).
  - **Universal rings do not iterate (w3-059).** The Promislow group is the
    amalgam `Klein *_(Z^2) Klein` of Lewin groups, and it has no universal ring.
    For locally indicable fundamental groups, the Linnell iteration is exactly
    FSP's open q:HF
    (`universal-division-rings-do-not-iterate-over-graphs-of-groups`). Over
    non-amenable edges, only Hughes-free/Linnell vertex rings can still iterate.
