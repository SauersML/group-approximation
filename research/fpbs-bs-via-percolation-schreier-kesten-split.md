---
rg: 2
id: fpbs-bs-via-percolation-schreier-kesten-split
kind: route
title: Split every nonamenable group by whether some infinite subgroup has a nonamenable Schreier graph
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-percolation-schreier-kesten-gap
  - fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness
  - fpbs-relative-gap-along-any-subgroup-separates
---

Let `Gamma` be nonamenable and finitely generated, `S` a finite symmetric
generating set, and `G = Cay(Gamma,S)`. Exactly one of the following holds.

**(α′) Some infinite subgroup `I` is not co-amenable.** By
`fpbs-percolation-schreier-kesten-gap`, `p_c(G) < p_c(I;G)`. Condition 1 of
`fpbs-relative-gap-along-any-subgroup-separates` holds, so `p_c(G) < p_u(G)`.

**(β′) Every infinite subgroup is co-amenable.** Then
`fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness` gives
`p_c(G) < p_u(G)`.

The dichotomy is exhaustive by definition. ∎

**How this refines the normal split.** Compare the route
`fpbs-bs-via-percolation-kesten-split` on origin/main. It splits on normal
subgroups with nonamenable quotient, and its residual class (β) is every
normally co-amenable group, which includes simple groups, higher-rank lattices
and Burger–Mozes groups.

- *(α′) contains (α).* For normal `N`, not co-amenable means nonamenable
  quotient.
- *(β′) is much smaller than (β).* By
  `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`, every
  (β′) group is periodic with no infinite amenable subgroup. So every
  nonamenable group with an element of infinite order moves into (α′), along
  a cyclic subgroup.

**Independent failure modes.**
- *(α′) can fail without refuting the goal.* An infinite subgroup of a product
  could have nonamenable Schreier graph and `p_c(I;G) = p_c(G)` while
  `p_c < p_u` holds on `G`, witnessed through another subgroup or directly.
- *(β′) can fail while (α′) holds.* A Tarski monster with `p_c = p_u` on some
  Cayley graph refutes (β′). It is untouched by (α′), which is vacuous for
  Tarski monsters.

**Honest scope.**
- *(α′) is at least as strong as the goal on some classes.* On groups with an
  infinite amenable wq-normal subgroup `I`, (α′) at `I` is equivalent to
  `p_c < p_u` (`fpbs-amenable-wq-normal-pu-is-relative-pc`).
- *What is gained.* One uniform percolation statement, calibrated and proved
  sharp on trees (`fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`),
  replaces the case analysis over normal subgroups, wq-normal subgroups and
  acylindrical hyperbolicity. The residual class is confined to periodic groups
  without infinite amenable subgroups.
