---
rg: 2
id: product-coefficient-fp-tests-elementary-directions
kind: claim
title: "Product-coefficient finiteness tests, the two directions used above FP_2: FP_n makes low homology commute with products, and a finitely generated non-FP_2 group has a product H_1 defect"
---

Let `k` be `Z` or `Q` and let `B` be a group.

**(a)** Suppose `B` is of type `FP_n(k)`. Then for every family `(M_i)_{i ∈ I}` of `kB`-modules, the
natural map `H_j(B; Π_i M_i) → Π_i H_j(B; M_i)` is an isomorphism for `j ≤ n − 1`.

**(b)** Suppose `B` is finitely generated and not of type `FP_2(k)`. Then there is a set `I` with
`H_1(B; Π_I kB) ≠ 0`. It can be taken countable when `B` is countable.

**Consequences used in the zaremsky 1.1 region.**

- If `B` is `FP_2(k)`, then `H_0` and `H_1` commute with products. So `H_1(B; Π_i F_i) = 0` for
  free `kB`-modules `F_i`.
- If `K` is `FP_3(k)`, then `H_2(K; Π_I kK) = Π_I H_2(K; kK) = 0` for every `I`.
- If a finitely generated `B` is not `FP_2(k)`, it has a nonzero product defect in degree 1.

These are the directions of the Bieri–Eckmann product criterion (Bieri, *Homological dimension of
discrete groups*, Section 1; Brown, *Cohomology of groups*, VIII.4) that
`split-edge-hnn-with-non-fp2-edge-is-not-fp3` uses. They are proved from scratch in the companion
route, so that theorem does not need the criterion as a literature input.
