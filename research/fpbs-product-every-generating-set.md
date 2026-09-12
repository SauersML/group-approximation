---
rg: 2
id: fpbs-product-every-generating-set
kind: claim
root: true
title: Every Cayley graph of a nonamenable direct product of two infinite groups has strict thresholds
distinct_from:
  fpbs-benjamini-schramm-universal: that is the universal goal over all nonamenable groups; this restricts to the direct-product class H x K but keeps the every-generating-set quantifier, and is Choi--Seo's explicitly posed open question for that class.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: those graph-level results already cover product generating sets whose factor is a tree, e.g. T_k x Z^d, via a nonunimodular automorphism group; this asks for the product class under every generating set, where the graph is a Cayley graph and hence unimodular.
  fpbs-sc-choi-seo: that carries the every-generating-set quantifier for acylindrically hyperbolic groups; a nonamenable direct product has infinite center or an infinite direct factor and is never acylindrically hyperbolic, so it lies exactly outside that theorem.
---

**OPEN.** Let `H` and `K` be infinite finitely generated groups with `H`
nonamenable, and let `G = H x K`. For every finite symmetric generating set `S`
of `G` not containing the identity,

```text
p_c(Cay(G,S)) < p_u(Cay(G,S)).
```

This is the direct-product case of `fpbs-benjamini-schramm-universal`, posed
explicitly by Choi--Seo (arXiv:2508.08932, Questions 1.3, 1.5 and 1.7): does
every Cayley graph of `F_2 x Z`, of `F_2 x F_2`, and of `CAT(0)` cubical groups
have a nonuniqueness phase. A nonamenable product is nonamenable, so a positive
answer is expected; the difficulty is the every-generating-set quantifier.

## Attempts

* **Product generating set (partial, known).** For the product generating set
  `S = S_H t S_K` the Cayley graph is the Cartesian product
  `Cay(H,S_H) x Cay(K,S_K)`. When a factor is free this is a tree times a
  graph, whose automorphism group is nonunimodular, so `p_c < p_u` follows from
  `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` (this already covers
  `T_k x Z^d`). Peres, *Percolation on nonamenable products at the uniqueness
  threshold* (Ann. IHP 36 (2000) 395--406), further studies the Cartesian
  product `X x Y` of infinite quasi-transitive graphs with `Aut(X)` nonamenable
  and shows the uniqueness-parameter set does not contain its infimum; its
  abstract gives only `N_infinity(p_u) != 1`, i.e. `N_infinity(p_u) in {0,
  +infinity}`, which separates the thresholds only in the `+infinity` branch
  (the numdam PDF could not be text-extracted to confirm the strong branch, so
  this is recorded as an import, not a verified separation). By
  `fpbs-nonuniqueness-parameter-criterion` it suffices to exhibit one
  nonuniqueness parameter; the partial results supply one for the Cartesian
  generating set.

* **Why the other class theorems miss it.**
  `fpbs-sc-choi-seo` needs acylindrical hyperbolicity, which a product with
  infinite center never has. Hutchcroft--Pan (arXiv:2409.12283, subgroup
  relativization) prove `N_infinity(p_u) = +infinity` only for a group with an
  amenable weakly quasi-normal subgroup of *exponential* growth (lamplighters);
  `Z` has polynomial growth and `F_2 x F_2` has no nontrivial amenable normal
  subgroup, so neither `F_2 x Z` nor `F_2 x F_2` is reached.

* **The obstruction to a naive transfer.** A generating set that mixes the two
  factors, containing some `(h,k)` with `h != 1 != k`, makes `Cay(G,S)` a
  non-Cartesian graph, so the factor structure that Peres and Grimmett--Newman
  use has no direct analogue. This is recorded as
  `fpbs-mixed-gen-set-not-cartesian` and it kills
  `fpbs-dead-product-peres-all-gens`.

* **Transfer attack (open).** The proposed route is to show that the property
  `N_infinity(p_u) = +infinity` is generating-set independent for a product, by
  using only the two commuting infinite subgroup actions of `H` and `K` (which
  exist for every generating set) together with indistinguishability of the
  infinite clusters (Lyons--Schramm), which holds for every unimodular
  transitive graph, hence every Cayley graph. If Peres's proof uses only these
  two ingredients and not the Cartesian metric, the transfer succeeds. Verifying
  this needs the proof of Peres 2000, not only its abstract; that check is the
  next step. The single structural input already in hand is that under
  uniqueness every open edge that disconnects the infinite cluster has exactly
  one infinite side (deletion tolerance), so pivotal edges for `o <-> x` are
  dangling bridges independent of `d(o,x)`.
