---
rg: 2
id: fpbs-normally-coamenable-class-nonuniqueness
kind: claim
title: Nonamenable groups all of whose infinite normal subgroups are co-amenable have strict thresholds on every Cayley graph
distinct_from:
  fpbs-residual-price-one-non-ah-class-nonuniqueness: that is the class of fixed price one, non-acylindrically-hyperbolic groups without infinite amenable wq-normal subgroups; this class is cut by normal subgroup structure instead, contains every simple nonamenable group and every higher-rank lattice, and excludes products such as T x T'.
  fpbs-percolation-kesten-normal-gap: that covers the complementary class, groups with an infinite normal subgroup of nonamenable quotient, through a relative threshold; this is the class where no normal relative threshold can help.
  fpbs-relative-threshold-commensurability-invariant: that kills relative-gap routes on groups whose infinite subgroups all have finite index; this class is larger and still allows non-normal infinite-index subgroups.
---

**OPEN.** Let `Gamma` be a finitely generated nonamenable group such that for
every infinite normal subgroup `N` of `Gamma`, the quotient `Gamma/N` is
amenable. Then for every finite symmetric generating set `S`,

```text
p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S)).
```

Call such groups **normally co-amenable**. The class contains:
* infinite simple nonamenable groups, including Burger--Mozes groups and
  simple Kazhdan groups;
* just-infinite nonamenable groups;
* irreducible lattices in higher-rank semisimple groups, by Margulis's normal
  subgroup theorem;
* Ol'shanskii's torsion Tarski monsters.

Such a group has no infinite amenable normal subgroup: an extension of an
amenable group by an amenable quotient is amenable.

**Why it is the second half.** Every nonamenable group either has an infinite
normal subgroup with nonamenable quotient, and is then covered by
`fpbs-percolation-kesten-normal-gap`, or is normally co-amenable. So this claim
and that one together, with `fpbs-relative-gap-along-any-subgroup-separates`,
give `fpbs-benjamini-schramm-universal`
(`fpbs-bs-via-percolation-kesten-split`).

**Independent failure modes.**
* **This claim could fail while the other holds.** A counterexample here would
  be a simple or just-infinite group with `p_c = p_u` on some Cayley graph. It
  would say nothing about products.
* **The other claim could fail without refuting Benjamini--Schramm.** A
  generating set of a product could have `p_c(N;G) = p_c(G)` for every normal
  `N` and still have `p_c < p_u`, witnessed through a non-normal subgroup or
  directly.

Known coverage inside the class: acylindrically hyperbolic members are covered
by Choi--Seo (`fpbs-sc-choi-seo`). For torsion Tarski monsters no relative
threshold route exists (`fpbs-relative-threshold-commensurability-invariant`).

## Attempts

* **Relative thresholds along subgroups with infinite normal core
  (2026-09-17, obstruction).** The natural route on this class is to feed some
  subgroup `I` into `fpbs-relative-gap-along-any-subgroup-separates`.
  `fpbs-amenable-quotient-normal-relative-threshold-is-pc` proves that for any
  infinite normal `N` with amenable `Gamma/N`, `p_c(N;G) = p_c(G)` on every
  Cayley graph. The proof counts Burton--Keane trifurcations over invariant
  random Folner cells of `Gamma/N`, and it uses only the cluster-count
  trichotomy. So for any `I` containing such an `N`, `p_c(I;G) = p_c(G)` and
  `chi^I_p = infinity` for all `p > p_c`. On a normally co-amenable group this
  holds for every `I` with infinite normal core.
  **Where it dies:** condition 1 of the separation criterion, for every member
  of the family and every generating set. The invariant is amenability of
  `Gamma/core(I)`.
  **What survives:** only subgroups with finite normal core, meaning faithful
  coset actions up to a finite kernel. For simple groups that is every proper
  infinite subgroup. Examples are the stabilisers in a Burger--Mozes group of a vertex
  of one tree factor, `SL_2(Z)`-type subgroups of higher-rank lattices,
  and `T` inside `T wr Z` for simple nonamenable `T`. There the relative
  threshold must come from the geometry of the coset action, not from the
  quotient.
  **Also recorded:** `fpbs-percolation-kesten-normal-gap` is now an iff where
  it holds. Under the split route, (alpha) and this hole partition the
  nonamenable groups exactly by whether some normal relative gap can exist at
  all.
