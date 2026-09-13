---
rg: 2
id: fpbs-residual-price-one-non-ah-class-nonuniqueness
kind: claim
title: Every Cayley graph of a fixed-price-one non-acylindrically-hyperbolic group without amenable wq-normal subgroups has strict thresholds
distinct_from:
  fpbs-no-amenable-wq-normal-class-nonuniqueness: that covers every nonamenable group with no infinite amenable wq-normal subgroup; this removes the groups not of fixed price one (Lyons) and the acylindrically hyperbolic groups (Choi--Seo), leaving the part that no cited theorem touches.
  fpbs-fixed-price-one-percolation-kernel: that covers all nonamenable fixed-price-one groups, including every group with an infinite amenable normal subgroup; this is the subclass that is also not acylindrically hyperbolic and has no infinite amenable wq-normal subgroup.
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**OPEN.** Let `Gamma` be a nonamenable finitely generated group such that

1. `Gamma` has fixed price one;
2. `Gamma` is not acylindrically hyperbolic;
3. no infinite amenable subgroup of `Gamma` is wq-normal.

Then every Cayley graph of `Gamma` has `p_c < p_u`.

**Structure of the class.** Use the intermediate-subgroup definition of
wq-normality (Peterson--Thom, arXiv:0708.4327, Lemma `alter`). Condition 3 then
says that every infinite amenable subgroup `A` lies in a proper subgroup `I`
with `g I g^(-1) ∩ I` finite for every `g notin I`. Such an `I` is the
intermediate subgroup witnessing that `A` is not wq-normal.
- By `fpbs-wq-normal-hull-is-almost-malnormal`, the smallest such `I` is the
  hull of `A`. It has infinite index and contains every `g` with
  `g A g^(-1) ∩ A` infinite.
- The class splits into two parts:
  - (R0): torsion groups with no infinite amenable subgroup;
  - (R1): groups with infinite amenable subgroups, all of whose hulls are
    proper.
- By `fpbs-amenable-splittings-are-ah-or-amenable-wq-normal`, no member is a
  nondegenerate amalgam or HNN extension over an amenable subgroup, and in
  particular not over a finite one. Stallings' theorem, which says that groups
  with more than one end split over finite subgroups, is not imported in the
  repo. With it, this would exclude groups with infinitely many ends.

**Members and candidates.** The torsion Tarski monsters of Ol'shanskii, and the
free Burnside groups `B(m,n)` with `m >= 2` and odd `n >= 1003`, are infinite
and nonamenable, and their amenable subgroups are all finite
(`fpbs-monster-groups-have-only-finite-amenable-subgroups`).
- **Members, in (R0).** Every `H x K` with `H` and `K` infinite, finitely
  generated, and with only finite amenable subgroups. Examples are `T x T'` for
  torsion Tarski monsters and `B(m,n) x B(m',n')`
  (`fpbs-residual-class-has-torsion-products`). So the class is nonempty. The
  route `fpbs-product-no-amenable-wq-normal-via-residual-class` makes
  `fpbs-product-no-amenable-wq-normal` the special case of products.
- **Member if and only if of fixed price one, then in (R0).** A single torsion
  Tarski monster, or a single `B(m,n)` in the range above.
  - Torsion groups are not acylindrically hyperbolic
    (`fpbs-osin-ah-groups-not-products-not-torsion`).
  - Hypothesis 3 is vacuous.
  - arXiv:2608.20472 proves that these `B(m,n)` have cost one. It states that
    fixed price one remains open for them.
- **Member if and only if of fixed price one, then in (R1).** A torsion-free
  Tarski monster with trivial center
  (`fpbs-torsion-free-tarski-monster-no-amenable-wq-normal`). One with
  nontrivial center is not a member, because its center is an infinite amenable
  normal subgroup.
- **Unsettled.**
  - Torsion groups with property (T) are not acylindrically hyperbolic and have
    cost one (`fpbs-kazhdan-groups-have-cost-one`). Their fixed price and
    hypothesis 3 are unchecked.
  - Large even Burnside groups have fixed price one
    (`fpbs-large-even-burnside-fixed-price`) and are torsion. Their
    nonamenability and hypothesis 3 are unchecked here.
- No member of (R1) is known unconditionally. The fixed price of Tarski monsters
  is not recorded in the repo or in the sources read for these nodes.

## Attempts

* **Every cited class misses it by definition.**
  - Lyons requires a group not of fixed price one.
  - Choi--Seo requires acylindrical hyperbolicity.
  - The relative susceptibility equivalence
    `fpbs-bs-iff-finite-relative-susceptibility` requires an infinite amenable
    wq-normal subgroup.

  **Where it stops:** no argument in the region uses the almost malnormal
  subgroups that condition 3 supplies.
* **Separation along a non-wq-normal subgroup.**
  `fpbs-relative-gap-along-any-subgroup-separates` needs no wq-normality. So for
  a torsion-free member one may take `I` to be a maximal cyclic subgroup, and a
  gap `p_c(G) < p_c(I;G)` would suffice.

  **Where it stops:** for almost malnormal `I` there is no estimate on
  `chi^I_p` above `p_c(G)`. The identity `p_c(I;G) = p_u(G)` is also
  unavailable, so this gives a sufficient condition only, not an equivalence.
* **Reduce to monsters with the hull.** Every member is either in (R0) or has
  almost malnormal hulls of infinite index around its infinite amenable
  subgroups. The known members are torsion products in (R0). The (R1)
  candidates depend on an unknown fixed price.

  **Where it stops:** this is structure, not a percolation estimate.
  - In (R0) there is no infinite amenable subgroup to take relative
    susceptibility along.
  - In (R1) the hulls are almost malnormal, which is the opposite of the
    overlap that the relative susceptibility route uses.
* **Exclude tree actions.** Nondegenerate splittings over amenable subgroups are
  excluded (`fpbs-amenable-splittings-are-ah-or-amenable-wq-normal`).

  **Where it stops:** splittings over nonamenable subgroups remain, and this
  removes no known member.
