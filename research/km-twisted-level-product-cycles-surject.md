---
rg: 2
id: km-twisted-level-product-cycles-surject
kind: claim
title: At every twisted level of the (2,4,6) codistance filtration the product graph cycles surject onto the matched local cycle spaces
distinct_from:
  km-codistance-filtration-twisted-levels-are-rank-two-pairs: that is the established structure theorem reducing the second homology of the development to this statement; this is the remaining finite combinatorial input.
  km-development-has-nonzero-end-cohomology-in-degree-one: that is the end-cohomology consequence; this implies it through contractibility of the development and is strictly stronger (it also gives type `F_infty`).
---

**OPEN (finite).**  For each twisted type of
`km-codistance-filtration-twisted-levels-are-rank-two-pairs` -- a pair
of rank-two residues of types in `{A_1 x A_1, B_2, G_2}` of the
`(2,4,6)` twin building over `F_q`, `q>1764^3`, twisted by a common
reflection `r` -- with `A`, `B` the panel-opposition subgraphs of the two
link polygons and the matched-class single-class vertex pairs
`(p',p'')`, the map

```text
H_1(A) (x) H_1(B)  -->  (+)_((p',p'')) Z_1( Lk_A(p') * Lk_B(p'') ),
c (x) c'  |-->  ( c|_(star p') (x) c'|_(star p'') )_((p',p''))       (TLS1)
```

is surjective.  Equivalently `H~_2(Omega)=0` for the twisted join
complex, equivalently the connecting maps of the filtration vanish at
that level.

If `(TLS1)` holds for all twisted types then, by the structure theorem,
`H_2(X)=0`: the Levi-triangle development is contractible, `Lambda` is
of type `F_infty`, `H^2(Lambda;Z Lambda)=H^2_c(X) != 0`, and
`compact-hyperbolic-km-lattices-fail-lp` follows (route
`km-lp-fails-via-development-end-cohomology` through
`km-development-has-nonzero-end-cohomology-in-degree-one`).

## Attempts

- **Grid type `A_1 x A_1` (either panel type): PROVED.**  `A` is
  `K_(q+1,q)` (all points against the lines other than `ell_1`), each
  class is one point, `H_1(A)` maps onto the tuples of zero-sum local
  vectors with zero total, and single-slot rank-one tensors `a (x) b`
  are differences of images of two product cycles; rank-one tensors
  span `Z_1(K_(q,q))`.
- **`B_2` and `G_2` types: reduced to connectivity.**  Single-class
  vertices are the points (or lines) far from the panel; each lies on
  exactly `q` lines of `A`; each such line meets every class once.  For
  a matched pair `(p'_0,p''_0)` of class `i` and target `a (x) b`, it
  suffices to find a cycle `c` of `A` through `p'_0` with prescribed
  zero-sum local vector `a` whose other vertices have classes in a set
  `C`, and a cycle `c'` of `B` through `p''_0` with classes in `C'`,
  `C cap C' = emptyset`, `i notin C cup C'`; then `(TLS1)` sends
  `c (x) c'` to `a (x) b` in the single slot `(p'_0,p''_0)`.  Such
  cycles exist as soon as the bipartite "class graphs" `G_C` (vertices:
  single-class vertices of classes in `C`; edges: lines of `A`, each
  joining its class-`C` points) connect the `q` lines through `p'_0`,
  which holds if `G_(jk)` is connected for `|C|=2`, and certainly if
  `G_C` is connected for `|C| ~ q/2`; `q+1 >= 5` classes leave room for
  disjoint `C, C'`.  Connectivity of these graphs in `W(q)`, `Q(4,q)`
  and the split Cayley hexagon `H(q)` for large `q` is the precise
  unverified step; it is a statement about collinearity between two
  "cones" of points over two points of a fixed line, and is expected
  from the expansion of generalized polygons.
- **Mixed types** (`J != J'`, e.g. grid against `B_2`) use the same
  argument with one side already settled.
