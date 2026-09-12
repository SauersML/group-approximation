---
rg: 2
id: two-regular-peeling-cores-carry-no-left-inverse
kind: claim
title: A crossed-product element whose stuck peeling core is two-regular has no left inverse in the anti-central summand
distinct_from:
  triangular-crossed-product-elements-are-units-or-zero-divisors: that decides elements whose peeling stops or terminates, using finitely supported kernel vectors; this decides stuck cores that are two-regular, using infinitely supported kernel vectors and the projection of partners into B.
  hyperfinite-coefficient-graphing-excludes-corner-witnesses: that is a counting obstruction on hyperfinite coefficient relations; this is a propagation obstruction on bi-infinite lines of the live core, which need no hyperfiniteness of the whole relation.
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Let `B = C(M_-, F_3) x| V ⊆ S_-`, and use the column peeling and fibre representations `rho_mu` of
`triangular-crossed-product-elements-are-units-or-zero-divisors`.

**Tools.**
- *Projection.* Keeping the `H`-supported part is a `B`-bimodule map `P : S_- -> B`. So a left inverse
  in `S_-` of an element of `B` can be replaced by one in `B`.
  - The same holds for Cohn families whose isometries lie in `B`, and for corner witnesses with `b' in B`.
  - So the filters of the artifact hold with partners anywhere in `S_-`.
- *All functions.* If `x in B` has a left inverse in `S_-`, every `rho_mu(x)` is injective on all
  functions `F_3^V`, and every `rho_mu(x*)` is surjective on `F_3[V]`.
- *Infinite back-substitution.* If the live operator at some peeling round kills a nonzero, possibly
  infinitely supported, function, then `x` has no left inverse in `S_-`.

**Theorem.** Let `x in B` be a non-unit. Suppose that at some round nothing is removed, every live column
has exactly two live points, and every live point lies in at most two live columns. Then `x` has no left
inverse in `S_-`.

**Proof.**
- *Two-regular.* Haar balance forces every live point into exactly two live columns, so each component of
  the live graph is a cycle or a bi-infinite line.
- *Lines.* Propagating a value along a line gives an infinite kernel vector.
- *Cycles.* Cycle lengths are bounded by compactness. A singular cycle block gives a finite kernel vector.
  If every block is invertible, `x` is a unit, which is excluded.

**Reading.** Survivors need, on positive measure, a live column with at least three live points or a live
point in at least three live columns. Pairwise mod-3 cancellation of overlapping pieces is dead.

Lemma 6.1, Proposition 6.2 and Corollary 6.3 of the artifact.

**ESTABLISHED 2026-09-12** by `two-regular-peeling-cores-proof`.
