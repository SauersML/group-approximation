---
rg: 2
id: fpbs-free-product-cayley-graphs-have-critical-l2-gap
kind: claim
title: Every Cayley graph of a free product on a union generating set has a critical L2 gap
distinct_from:
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that gives p_c < p_u on hyperbolic graphs and on graphs with a nonunimodular automorphism subgroup; this gives p_c < p_{2->2} on free-product Cayley graphs, including graphs whose automorphism group is the group itself, such as Heisenberg * Z/2 on a union generating set.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is the open conjecture for every nonamenable transitive graph; this settles only Cayley graphs of free products on unions of factor generating sets.
  fpbs-expanding-factor-product-strict-thresholds: that is perturbative, for Cartesian products with a strongly expanding factor; this is not perturbative, assumes no expansion and allows amenable factors.
  fpbs-pivotal-triangle-fails: that uses the free-product block structure to refute a pivotal triangle inequality on C6 * C2; this uses it to bound the critical connectivity operator.
artifacts:
  - research/artifacts/fpbs/docs/free-product-critical-l2-2026-09-12.md
---

**ESTABLISHED.** Let `n >= 2`, and let `H_1, ..., H_n` be nontrivial finitely
generated groups. Let `S_i` be a finite symmetric generating set of `H_i` with `e`
not in `S_i`. Put `S = S_1 ⊔ ... ⊔ S_n` and
`X = Cay(H_1 * ... * H_n, S)`. Exclude the line: `n = 2` with `|H_1| = |H_2| = 2`.
Then

```text
||T_{p_c}||_{2->2}  <=  lambda  <  infinity,
p_{2->2}(X) - p_c(X)  >=  (1 - p_c(X)) / (|S| lambda).
```

Here `lambda` is explicit in terms of the factor connection probabilities at
`p_c`. It is formula (2.3) of the artifact.

So Hutchcroft's L2 boundedness condition `p_c(X) < p_{2->2}(X)` holds. The
triangle condition at `p_c` also holds, with `nabla_{p_c} <= lambda^3`.
Nothing is assumed about the factors, which may be amenable.

Some of these graphs lie outside the non-perturbative classes in the sources.
Take `Heisenberg * Z/2`, on a union generating set whose Heisenberg part has no
extra automorphisms (Leemann–de la Salle, arXiv:2010.06020). That graph:

- has `Aut(X) = Gamma`;
- is not hyperbolic;
- is not a product with a tree;
- has spectral radius at least `4/5`.

The perturbative papers on large Cheeger constant and high girth were not
re-read.

Credit: Kozáková proved the formulas for `chi_p` and `p_c` on free products
(arXiv:math/0611668, Theorems 1–2 and Corollaries 3–4). Nothing in that paper
treats `T_p` as an operator or `p_{2->2}`. The proof imports two statements
quoted in Hutchcroft, arXiv:1804.10191: sharpness, from the display before
Proposition 2.3, and Corollary 2.6.

Proof:
`fpbs-free-product-block-tree-spectral-proof`.
