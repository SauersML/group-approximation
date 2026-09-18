---
rg: 2
id: fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness
kind: claim
title: Nonamenable groups all of whose infinite subgroups are co-amenable have strict thresholds on every Cayley graph
distinct_from:
  fpbs-no-amenable-wq-normal-class-nonuniqueness: that class only excludes infinite amenable wq-normal subgroups and contains products T x T', torsion-free groups and higher-rank lattices; this class has no infinite amenable subgroup at all, is periodic, and contains none of those.
  fpbs-residual-price-one-non-ah-class-nonuniqueness: that is cut by fixed price one, acylindrical hyperbolicity and wq-normal subgroups; this is cut purely by co-amenability of infinite subgroups, excludes every group with an element of infinite order, and makes no cost assumption.
  fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap: that proves the structure of this class (periodic, no infinite amenable subgroup, normally co-amenable); this conjectures nonuniqueness on it.
  fpbs-normally-coamenable-class-nonuniqueness: that class only requires infinite normal subgroups to be co-amenable and contains simple nonamenable groups, Burger–Mozes groups and higher-rank lattices; this class requires every infinite subgroup to be co-amenable, is a proper subclass of it, is periodic, and excludes all of those.
---

**OPEN.** Let `Gamma` be a finitely generated nonamenable group in which every
infinite subgroup `I` is co-amenable, meaning there is a `Gamma`-invariant mean
on `ℓ^∞(I\Gamma)`. Then for every finite symmetric generating set `S`,

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

**What the class is.**
- *Structure* (`fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`,
  part (c)). Every member is periodic, has no infinite amenable subgroup, and
  has amenable quotients by all infinite normal subgroups. So the class sits
  inside the normally co-amenable groups.
- *Members.* Every nonamenable group whose infinite subgroups all have finite
  index, in particular Ol'shanskii's nonamenable Tarski monsters.
- *Excluded.* Every nonamenable group with an element of infinite order, so
  every torsion-free group, every finitely generated linear group, every
  acylindrically hyperbolic group, every higher-rank lattice and every
  Burger–Mozes group. Also every product `T x T'` with `T` infinite and `T'`
  nonamenable.
- *Undecided.* Whether a free Burnside group `B(m,n)` of large odd exponent lies
  here depends on whether it has an infinite amenable or non-co-amenable
  subgroup. That is not decided here.

**Why it is the second half.** Every nonamenable group either has an infinite
subgroup that is not co-amenable, and is then covered by
`fpbs-percolation-schreier-kesten-gap`, or lies in this class. See
`fpbs-bs-via-percolation-schreier-kesten-split`.

**Known coverage inside the class.**
- *Fixed price.* Members of fixed price `> 1` are covered by Lyons' cost
  criterion.
- *Relative thresholds give nothing.* No relative-threshold route is available:
  - on the tree, co-amenable subgroups have no gap
    (`fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`, item 2);
  - for subgroups of finite index the relative threshold is the global one.
- *So this is the exact home of the goal's hard core.* Its members are periodic
  groups where every percolation argument must be global.

## Attempts

* **2026-09-18, relative thresholds on the whole class (swarm-0917-w7-w7-bs-break).**
  Dead as a route, and now proved dead on every Cayley graph, not only on the
  tree. `fpbs-co-amenable-subgroup-relative-threshold-is-pc` proves
  `p_c(I;G) = p_c(G)` and `chi^I_p = infinity` for all `p > p_c(G)`, for
  every co-amenable `I`, normal or not, on every Cayley graph. So on this class
  every infinite subgroup is blind.
  * **Where it dies:** condition 1 of
    `fpbs-relative-gap-along-any-subgroup-separates`, for every subgroup at once.
  * **Invariant:** a Folner set of `Sch(I\Gamma,S)`, pulled back to a union
    of `I`-orbits, on which mass transport along the free `I`-action forces
    trifurcation density at most `|∂F|/|F|`.
  * **Consequence:** a proof on this class cannot pass through any subgroup.
    It must separate `p_c` from `p_u` by a global argument, which is the
    goal itself restricted to the class.
