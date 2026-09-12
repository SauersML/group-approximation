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
explicitly by Choi--Seo (arXiv:2508.08932v2, Questions 1.3, 1.5 and 1.7, read
from source 2026-09-11): does every Cayley graph of `F_2 x Z`, of `F_2 x F_2`,
and of `CAT(0)` cubical groups have a nonuniqueness phase. The same paper
records that Hutchcroft informed the authors that Question 1.3 is still not
answered. By `fpbs-nonuniqueness-parameter-criterion` it suffices to exhibit,
for each generating set, one parameter with infinitely many infinite clusters.

## Attempts

* **Tree factor with a free basis (partial, known).** When `S = S_H t S_K`
  and `S_H` is a free basis of a free factor `H = F_n`, the Cayley graph is the
  Cartesian product of a regular tree with `Cay(K,S_K)`. The end stabilizer of
  the tree times `Aut(Cay(K,S_K))` is a nonunimodular quasi-transitive subgroup,
  so `p_c < p_u` follows from `fpbs-hyperbolic-and-nonunimodular-nonuniqueness`
  (this covers `T_k x Z^d`). **Where it stops:** a generating set of `F_n` that
  is not a free basis gives a factor graph that is not a tree, and a mixed
  generating set gives a non-Cartesian graph (`fpbs-mixed-gen-set-not-cartesian`);
  in both cases the nonunimodular structure is lost.

* **Tree-projected mixed sets of `F_n x Z` (partial, 2026-09-12).** The structure
  is not always lost. For generating sets projecting into a free basis, its
  inverses and `1`, lifted tree automorphisms give a closed quasi-transitive
  nonunimodular subgroup in two cases:
  * some decoration set is symmetric up to translation
    (`fpbs-tree-projected-reversible-letter-nonunimodular`);
  * two decoration sets agree up to translation and reflection
    (`fpbs-tree-projected-letter-exchange-nonunimodular`).

  **Where it dies:** rigid decorations. For
  `{(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}` the whole automorphism group is
  discrete (Section 3 of
  `research/artifacts/fpbs-f2xz-all-generating-sets-2026-09-12.md`), so
  Question 1.3 cannot be reduced to Hutchcroft's theorem. Choi–Seo Question 1.3,
  verbatim from the TeX source (2026-09-12): "Does every Cayley graph of
  $F_{2} \times \Z$ have a nonuniqueness phase?"

* **Nonuniqueness at the uniqueness threshold (weak form only).** Peres,
  *Percolation on nonamenable products at the uniqueness threshold*, Ann. IHP 36
  (2000) 395--406, Theorem 1.1 (read from source 2026-09-11): on the Cartesian
  product `X x Y` of infinite quasi-transitive graphs with `Aut(X)` nonamenable,
  `P_{p_u}(there is a unique infinite cluster) = 0`. Hutchcroft--Pan,
  arXiv:2409.12283v1, Theorem 1.14 with Definition 1.11 (read from source):
  `H x K` with `H` finitely generated nonamenable and `K` infinite finitely
  generated is an obstacle to uniqueness, so **every** Cayley graph of it has
  no unique infinite cluster at `p_u`. Their Definition 1.11 states explicitly
  that this means either no infinite cluster or infinitely many. The slicing
  argument extends to every Cayley graph of any `Gamma = HK` with commuting
  subgroups, `H` finitely generated nonamenable and `K` infinite
  (`fpbs-pu-nonuniqueness-commuting-subgroups`). **Where it dies:**
  `fpbs-pu-nonuniqueness-cannot-separate` shows that this weak conclusion is
  consistent with `p_c = p_u` and adds nothing to threshold separation, killing
  `fpbs-dead-pu-nonuniqueness-separates`.

* **Why the other class theorems miss it.** `fpbs-sc-choi-seo` needs
  acylindrical hyperbolicity, which a product with an infinite direct factor
  never has. Hutchcroft--Pan Theorem 1.13 needs an amenable wq-normal subgroup
  of *exponential* growth; `Z` has polynomial growth and `F_2 x F_2` has no
  nontrivial amenable normal subgroup. Lyons's cost criterion
  (`fpbs-non-fixed-price-one-has-nonuniqueness`) is silent because products of
  infinite groups with an element of infinite order have fixed price one.

* **What is actually needed.** For a fixed Cayley graph of `H x K`, one
  parameter `p > p_c` with more than one infinite cluster; equivalently, since
  `N_infinity(p_c) = 0` (`fpbs-critical-no-infinite-cluster`), an infinite
  cluster at `p_u` together with the weak theorem above. Hutchcroft--Pan (page
  2, read from source) state that it is not even known whether the number of
  infinite clusters at `p_u` of a Cayley graph depends on the generating set.
  No method in the region supplies an infinite cluster at `p_u` for a mixed or
  non-free-basis generating set; this is the open core.
