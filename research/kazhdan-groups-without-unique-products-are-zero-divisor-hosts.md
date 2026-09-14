---
rg: 2
id: kazhdan-groups-without-unique-products-are-zero-divisor-hosts
kind: claim
title: Infinite torsion-free Kazhdan groups without unique products escape the unique-product, amenable, special and class-C cases of the zero-divisor conjecture, and Tarski monsters among them escape every linear group
distinct_from:
  zero-divisor-support-subgroup-host-constraints: that lists what a zero-divisor host must violate; this exhibits hosts that violate all of it except, in characteristic zero, Strong Atiyah, which is unknown for them.
  zero-divisor-host-is-not-virtually-compact-special: that excludes subgroups of virtually compact special groups and of 3-manifold groups as hosts; this shows that hosts without unique products escape the special exclusion and the other known cases.
  e33-no-unique-product-pairs-of-small-radius: that is a SAT census on E_3(3), which is not known to lack unique products and is a host only outside characteristics 0 and 3; this is about hosts that provably lack them and offer no exact multiplication for a census.
  arzhantseva-steenbock-kazhdan-groups-without-unique-products: that imports the existence of the groups; this checks them against the known cases of the conjecture.
  congruence-kazhdan-groups-satisfy-strong-atiyah: that exhibits Kazhdan groups inside p-adic congruence kernels, where the conjecture holds in characteristics 0 and p; this is about Kazhdan groups without unique products, and shows that the Tarski monsters among them lie in no congruence kernel.
---

**ESTABLISHED.** Let `G` be an infinite torsion-free group with property (T)
and without unique products. Then:
1. `G` is not elementary amenable;
2. `G` is not a subgroup of any torsion-free virtually compact special group;
3. `G` is not in Linnell's class `C`;
4. `G` is not locally indicable;
5. if all proper subgroups of `G` are cyclic, then `G` is not residually
   finite. So it is not linear over any field, and it is not a subgroup of any
   p-adic congruence kernel
   `CS(u,d,p) = {A in Mat_d(Z_p) : A = I mod p^u}`.

Such groups exist, including:
- word-hyperbolic ones;
- Kazhdan subgroups of torsion-free direct limits of hyperbolic groups;
- Tarski monsters.

See `arzhantseva-steenbock-kazhdan-groups-without-unique-products`.

**Consequence.** `kaplansky-zero-divisor-conjecture` lists the cases where the
conjecture is known:
- unique-product groups;
- torsion-free elementary amenable groups;
- in characteristic zero, groups satisfying Strong Atiyah;
- subgroups of torsion-free virtually compact special groups and of compact
  3-manifold groups;
- over fields of characteristic 0 or `p`, subgroups of `p`-adic congruence
  kernels (Farkas--Linnell,
  `p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`).

The hypothesis and items 1--2 rule out unique products, elementary amenability
and the special case. Items 3--4 rule out two classes on which Strong Atiyah is
proved, Linnell's class `C` and locally indicable groups.
- No source read here proves Strong Atiyah or the zero-divisor conjecture for
  any such `G`.
- Arzhantseva--Steenbock record the conjecture as unknown for their hyperbolic
  examples.

How far each kind of host escapes:
- **Tarski monsters of Corollary 2: every case above, over every field.** Item
  5 rules out congruence kernels. Compact 3-manifold groups are residually
  finite (Hempel, with geometrization), so item 5 rules those out too. So these
  are characteristic-0 hosts. `E_3(3)` is not one: it lies in a 3-adic
  congruence kernel (`congruence-kazhdan-groups-satisfy-strong-atiyah`).
- **Hyperbolic examples and the subgroups `N`: every case except congruence
  kernels and 3-manifold groups, which stay possible.** An embedding into
  either would make them residually finite. Residual finiteness of hyperbolic
  groups is Open problem 2 of the source.

**A Tarski-monster host needs its whole group.** Let `M` be a group from
Corollary 2 of the source, all of whose proper subgroups are cyclic. If
`alpha beta = 0` with `alpha, beta` nonzero in `k[M]`, then
`<supp alpha ∪ supp beta> = M`.

**No ball census here.**
- The hyperbolic examples have solvable word problem.
- Corollary 1 is proved either through random labelled graphs or through
  Ol'shanskii's quotient theorem.
- This graph records no concrete presentation or normal form for any of these
  groups.

So no exact Cayley ball is available. The SAT censuses in
`experiments/zero-divisor-tf/` stay on `E_3(3)`. It has exact multiplication
but is not known to lack unique products, and it is a host only outside
characteristics 0 and 3.

DERIVATION
[[kazhdan-non-up-zero-divisor-hosts-proof]]
