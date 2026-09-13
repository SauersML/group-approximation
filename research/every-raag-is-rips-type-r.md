---
rg: 2
id: every-raag-is-rips-type-r
kind: claim
title: Every right-angled Artin group with its standard generating set is of Rips type R
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for Z^n, the RAAGs on complete graphs; this claims type R for the RAAG on every finite graph
---

For every finite simplicial graph `Γ` there is `r_0(Γ)` such that for all
`r ≥ r_0(Γ)` the Rips complex `R_r(A_Γ, V(Γ))`, built on the word metric of
the standard generators, is contractible.

This is the affirmative answer to Zaremsky Problem 4.5
(`zaremsky-4-05-raag-rips-complexes-contractible`). Its negation is
`some-raag-is-not-rips-type-r`.

Hulbert–Zaremsky (arXiv:2608.25614) predict the stronger form: `R_t(A_Γ)` is
contractible for every `t ≥ n`, where `n` is the size of a largest clique in
`Γ` (the cohomological dimension of `A_Γ`).

## Attempts

- **Covered classes.** Complete `Γ` (Virk); triangle-free `Γ`
  (Li–Sánchez Saldaña, Theorem 1.5); and, through their free-product closure
  (Theorem 1.3), every `Γ` whose connected components are cliques or
  triangle-free (`raags-with-clique-or-triangle-free-components-are-type-r`).
- **2026-09-13, products of free groups (UNREVIEWED).** Complete multipartite
  `Γ`, `A_Γ = F_{n_1} × ⋯ × F_{n_k}`, are of type R with `r_0 = k(k+1) − 1`
  (`complete-multipartite-raags-are-rips-type-r`). The proof verifies
  Zaremsky's criterion (arXiv:2410.11993, Theorem 3.1) for l^1 products of trees
  through tree barycentres, Helly number `k+1` and rounding
  (`l1-products-of-trees-have-contractible-rips-complexes`). With the
  free-product closure this covers every `Γ` whose components are complete
  multipartite or triangle-free
  (`raags-with-multipartite-or-triangle-free-components-type-r`), including
  `F_2 × F_2 × F_2` and `Z^2 × F_2`.
- **Next obstacle.** The smallest uncovered graph is the triangle with a
  pendant vertex, `A_Γ = Z × (Z^2 * Z)`. The criterion argument needs a
  barycentre with the Jensen bound `d_1(x,b) ≤ ∫ d_1(x,y) dμ` in the Salvetti
  cover. For products of trees it comes coordinatewise from Lemma J. For
  `Z^2 * Z` (a tree of l^1 planes and lines glued at vertices) a candidate is
  the barycentre in the tree-graded CAT(0) realization, with Jensen proved by
  the same first-variation argument across the gluing points. That is not
  checked yet.
- **Where the imported methods stop.** Li–Sánchez Saldaña glue Rips-contractible
  pieces along sets of diameter ≤ 1 around a point (their Corollary 2.5), which
  is how squares assemble into a two-dimensional Salvetti cover. They call the
  higher-dimensional gluing combinatorics "intractable" and ask whether finite
  edge groups can be replaced by type R edge groups. The amalgam
  `Z^3 *_Z Z^2` (a triangle with a pendant vertex) needs exactly that, with
  an infinite cyclic edge group.
- **Crushing points cannot come from geodesics to the origin in dimension ≥ 3
  (checked by hand).** In `Z^{n+1}` with `n ≥ 3`, take `x = (M,…,M,0)` and
  `a_i = x − (r/2)e_i + (r/2)e_{n+1}` for `i ≤ n` (`r` even, `M > r`). Then
  `|a_i| = |x|`, `d(a_i,x) = r` and `d(a_i,a_j) = r`, so `A = {x, a_1,…,a_n}` is a
  simplex. Every `y` on a geodesic from `x` to `0` is `y = x − D` with `D ≥ 0`
  supported on the first `n` coordinates, and then
  `d(a_i,y) = r + |D|_1 − 2D_i` (when `D_i ≤ r/2`). Requiring `|D|_1 ≤ 2D_i`
  for all `i ≤ n` forces `D = 0`. So no point of the interval `I(0,x)` other
  than `x` stays within `r` of `A`. A sideways point does:
  `y = x − (1,…,1,0) + (n−1)e_{n+1}` has `|y| = |x| − 1`, `d(x,y) = 2n − 1` and
  `d(a_i,y) = r − 1`. Crushing sets for RAAGs of dimension ≥ 3 therefore have to
  leave geodesic intervals toward the base point. Hyperbolic-group arguments and
  the pure interval pushes of discrete Morse theory on word length both push
  along those intervals.
- **Plan (in progress).** Use Virk's local crushing (arXiv:2405.09134,
  Definition 3.6 and Theorem 3.7) on an exhaustion by finite sets, removing a
  point of maximal word length at each step (ties broken by a secondary
  potential such as the squared CAT(0) distance), then pass to the union
  (Li–Sánchez Saldaña, Lemma 2.1: an increasing union of Rips-contractible
  subspaces is Rips-contractible). The crushing set `L_x` is a set of diameter
  `≤ r` near `x`, built from walls (hyperplanes) adjacent to `x`, and not
  confined to `I(e,x)`. The first targets are `F_2 × F_2 × F_2`, `Z^2 × F_2`
  and `Z^3 *_Z Z^2`.
