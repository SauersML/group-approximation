---
rg: 2
id: fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable
kind: claim
title: On any product of regular trees and an amenable Cayley graph, an infinite subgroup has a relative threshold gap iff it is not co-amenable, and on a tree times any graph the section-growth barrier beta = q is exactly co-amenability of the tree section
distinct_from:
  fpbs-percolation-schreier-kesten-gap: that conjectures the iff on every Cayley graph of every group; this proves it on the class T_1 x ... x T_n x Cay(A) with A amenable, the first class beyond single trees on which the full statement holds, and names the exact residual on T x H.
  fpbs-tree-product-thin-section-subgroups-have-tilt-gap: that proves the gap on T x H under the hypothesis beta(I) < q, which it computes only for finite-index or virtually cyclic sections and names beta(I) = q as the barrier; this proves the uniform coset bound beta(I) <= max(sqrt q, mu_+((q+1) rho_J)) < q for every non-co-amenable tree section, so the barrier is exactly co-amenability of J(I), and removes it on tree products.
  fpbs-tree-subgroup-relative-gap-iff-not-co-amenable: that decides the gap on a single tree through the growth of J itself; this bounds the growth of every left coset of J uniformly, which is what sections of subgroups of products need, and works with any number of tree factors and an amenable factor.
  fpbs-co-amenable-subgroup-relative-threshold-is-pc: that proves no co-amenable subgroup has a gap on any Cayley graph; this uses it for the only-if direction and proves the if direction on tree products.
  fpbs-percolation-kesten-normal-gap: that conjectures the gap for normal subgroups with nonamenable quotient on every Cayley graph; this proves it, and the gap along every infinite amenable subgroup, on the tree-product class for product generators.
artifacts:
  - experiments/fpbs-coset-sections-2026-09-17/check_coset_sections.py
  - experiments/fpbs-coset-sections-2026-09-17/output.txt
---

**ESTABLISHED.** Proof route:
`fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable-proof`.

**Setting.**
- A **tree factor** is `T = Cay(Lambda, S_Lambda)` that is the `k`-regular
  tree, `k >= 3`, `q = k - 1`. For example `F_d` with a free basis, or any
  free product of copies of `Z` and `Z/2` with the standard generators.
  `S_m` is the sphere of radius `m` about `1` in `Lambda`.
- For `J <= Lambda`, `rho_J = ||P_Sch(J\Lambda, S_Lambda)||` is the norm of
  simple random walk on the Schreier graph of right cosets. Co-amenability is
  as in `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`.
- `mu_+(x) = (x + sqrt(x^2 - 4q))/2` for `x >= 2 sqrt q`, and
  `mu_+(x) = sqrt q` otherwise. It is nondecreasing and `mu_+(q+1) = q`.
- Products are Cartesian products of Cayley graphs, the Cayley graph of the
  product group for the disjoint union of the generating sets. Section
  growth `beta(I)`, tree section `J(I)`, `chi^I_p` and `p_c(I;G)` (either
  definition) are as in
  `fpbs-tree-product-thin-section-subgroups-have-tilt-gap`.

**Theorem.**

1. **Uniform coset counts (Lemma A).** Let `J <= Lambda`. For every
   `y in Lambda` and every `m >= 0`,

   ```text
   #(yJ ∩ S_m) <= (1 + 1/q) (m + 1) r_J^m,     r_J = mu_+((q+1) rho_J).
   ```

   If `J` is not co-amenable, then `rho_J < 1`, so `r_J < q`.
2. **The barrier is co-amenability.** Let `G = T x H` with `H` any Cayley
   graph, and `I <= Lambda x H_grp` infinite. Then

   ```text
   beta(I) < q   iff   J(I) is not co-amenable in Lambda,
   ```

   and in that case `beta(I) <= r_(J(I))`. So the hypothesis of
   `fpbs-tree-product-thin-section-subgroups-have-tilt-gap` item 2 holds for
   every infinite `I` whose tree section is not co-amenable, and
   `p_c(G) < p_c(G,Gamma_xi,lambda) <= p_c(I;G)` for every `lambda in (0,1)`
   with `q^(max(lambda,1-lambda)) > r_(J(I))`. If moreover
   `rho_(J(I)) <= 2 sqrt q/(q+1)`, the Kesten value of the tree itself, then
   `p_c(I;G) >= p_t`.
3. **Schreier–Kesten gap on tree products.** Let

   ```text
   G = T_1 x T_2 x ... x T_n x Cay(A, S_A),     n >= 1,
   ```

   with tree factors `T_i = Cay(Lambda_i, S_i)` of degrees `k_i >= 3`, and `A`
   any finitely generated amenable group with any finite generating set
   (`A` trivial allowed). For every infinite `I <= Lambda_1 x ... x Lambda_n x A`:

   ```text
   p_c(G) < p_c(I;G)   iff   I is not co-amenable.
   ```

   If `I` is not co-amenable, some coordinate section `I ∩ Lambda_i` is not
   co-amenable in `Lambda_i`, and item 2 applies with `T = T_i`.

**Corollaries on the class of item 3** (product generators only).

- **Percolation Kesten normal gap.** Every infinite normal `N` with
  nonamenable quotient has `p_c(G) < p_c(N;G)`. For normal `N`, co-amenable
  means amenable quotient.
- **Amenable subgroups.** Every infinite amenable subgroup has a gap, since
  `Gamma` is nonamenable (`n >= 1`) and amenable subgroups of nonamenable
  groups are not co-amenable (part (b) of
  `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`).
- **Cutoff.** The gap along `I` depends only on whether `I` is co-amenable.
  Where it holds, it is certified by an explicit end tilt, whose window
  `q_i^(max(lambda,1-lambda)) > r_(J_i)` depends only on the Kesten norm of
  one coordinate section.

**Residual on `T x H` for general `H` (named).** By item 2, the only subgroups
of `Lambda x H_grp` that end tilts toward the ends of `T` cannot certify are
those with `J(I)` co-amenable in `Lambda`. For such a subgroup to be
non-co-amenable (the only case in which a gap can hold), all of the following
must be true:
- `H_grp` is nonamenable;
- `K(I) = I ∩ H_grp` is not co-amenable in `H_grp`, since otherwise
  `J(I) x K(I) <= I` is co-amenable;
- `H` is not itself a tree product with amenable factor, by item 3.

By Goursat, `I` sits in `pi_1(I) x pi_2(I)` as the graph of an isomorphism
`pi_1(I)/J(I) ≅ pi_2(I)/K(I) = Q`. The residual splits into two cases.
- **(R-slab) `Q` amenable.** Then `pi_1(I)` is co-amenable in `Lambda`,
  `I` is co-amenable in `pi_1(I) x pi_2(I)`, and so, by transitivity of
  co-amenability, `pi_2(I)` is not co-amenable in `H_grp` (Step 5 of the
  route). The model case is `Lambda x K`: the percolation
  Kesten gap for the tree-factor fibre `N = Lambda x 1` with quotient `H_grp`.
- **(R-graph) `Q` nonamenable.** `I` is the graph of an isomorphism between
  nonamenable quotients. This is a genuine diagonal case, with no product
  structure.

So on products with a tree factor, the whole of
`fpbs-percolation-schreier-kesten-gap` reduces to subgroups whose projection
to `H_grp` is non-co-amenable. These are handled by the other factor, which
has no end to tilt toward unless it is again a tree product.

**What this does and does not advance.**
- *Advances.* It is the first class of non-tree Cayley graphs on the board on
  which the full Schreier–Kesten statement is proved, as an iff and for every
  subgroup. No literature search beyond the board was made.
  It includes `F_2 x F_2`, the named test group of the product lane, where
  subgroups such as `F_2 x K` with `K` non-co-amenable (for example
  `F_2 x <a>`) were outside the w15 theorem. It converts the named w15
  barrier `beta(I) = q` into the exact algebraic condition "`J(I)`
  co-amenable". The obstruction for end tilts on `T x H` is therefore the
  residual above, and not anything weaker.
- *Does not advance.* It does not advance `fpbs-benjamini-schramm-universal`
  itself: every graph in the class is a product with a tree factor, so it
  already has `p_c < p_u` by Hutchcroft. The method needs a transitive
  nonunimodular automorphism group with a radial two-point function, as in
  w15.

**Numerical check** (`artifacts`).
- (a) `A_n = P_n(A_1)`, and the entries of `A_n` equal the coset counts, on a
  random 40-point Schreier graph of `F_2` for `n <= 7`.
- (b) The Chebyshev bound, on a grid for `q = 2, 3, 4, 6` and `n < 40`. The
  worst ratio is `0.857`.
- (c) `sup_y #(yJ ∩ S_m)` for `J = <a, b a b^-1>` in `F_2`, `m <= 11`. It
  strictly exceeds `#(J ∩ S_m)` at `m = 2, 3, 7, 8, 9`, so the uniformity over
  cosets is not automatic. Its `m`-th root stays near `1.95 < q = 3`.
