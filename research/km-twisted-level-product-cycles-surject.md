---
rg: 2
id: km-twisted-level-product-cycles-surject
kind: claim
title: At every twisted level of the (2,4,6) codistance filtration the product graph cycles surject onto the matched local cycle spaces
distinct_from:
  km-codistance-filtration-twisted-levels-are-rank-two-pairs: that is the established structure theorem reducing the second homology of the development to this statement; this is the remaining finite combinatorial input.
  km-development-has-nonzero-end-cohomology-in-degree-one: that is the end-cohomology input for Corollary D; this is the finite combinatorial statement that makes the thick part 2-connected (type `F_3`) and identifies that input with `H^2_c` of the thick part, without deciding it.
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
`H_1(X^)=H_2(X^)=0` for the bottom thick part `X^=Z_(<=0)` of the
twin-building product: `X^` is 2-connected, `Lambda` is of type `F_3`
(a new finiteness property for these lattices), and
`H^2(Lambda;Z Lambda)=H^2_c(X^)`.  Corollary D then reduces to
`H^2_c(X^)!=0`, equivalently `H^3_c` of the cusp region `Z minus X^`;
this last step is open (the development `X` has `H_2!=0`, so its point
class is unavailable).

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
- **`B_2` via the symplectic quadrangle: two classes fail, three
  suffice (2026-08-23).**  Model the `B_2` residue as `W(q)`: points of
  `PG(3,q)`, lines the totally isotropic lines, `ell_1` a t.i. line,
  classes indexed by its points `p_i`, class-`j` points forming the
  affine plane `pi_j - ell_1` with `pi_j = p_j^perp`.  The two-class
  graph is computed EXACTLY: the class-`k` neighbours of a class-`j`
  point `P` are the line `(span(P,p_k))^perp = P^perp cap pi_k`, which
  passes through `p_j`, and the two-step reachable set collapses onto
  the single line `span(P,p_k)`: `G_(jk)` is a disjoint union of `q`
  complete bipartite graphs `K_(q,q)` (components: a line through `p_k`
  in `pi_j` paired with a line through `p_j` in `pi_k`).  So the
  two-class path construction FAILS for `B_2`.  With a third class `l`
  it succeeds: the class-`l` neighbours of `P` form a line through
  `p_j` in `pi_l`, and as `Q` runs over it the lines
  `Q^perp cap pi_k` run injectively over the whole pencil of lines
  through `p_l` in `pi_k` (their common point is
  `span(P,p_l) cap pi_k = {p_l}`), so every class-`k` point off a
  plane's worth of exceptions is reachable from `P` in two steps.
  Hence for `q` large the three-class graphs are connected with room to
  avoid `ell_1`-meeting lines, prescribed local vectors at `p'_0` are
  realized by cycles with intermediate classes in a 3-set `C`, and
  disjoint 3-sets `C, C'` (available for `q+1 >= 7`) make `(TLS1)`
  surjective for `B_2 x B_2` and mixed `B_2` levels, modulo the dual
  quadrangle `Q(4,q)` for odd `q` (same computation in the orthogonal
  model) and orientation bookkeeping.  The `G_2` case (split Cayley
  hexagon) awaits the analogous pencil computation.
- **`G_2` setup (2026-08-23).**  Model the hexagon residue as the split
  Cayley hexagon `H(q)` on the parabolic quadric `Q(6,q)`: two points
  are hexagon-collinear iff one lies in the other's hexagon plane
  `pi_x` (the plane containing the `q+1` lines through `x`), at
  distance four iff perpendicular but not collinear, opposite iff not
  perpendicular.  For the line-panel `ell_1` with classes its points
  `p_i`, the class-`i` single-class vertices are
  `p_i^perp cap Q(6,q) minus (ell_1^perp cup pi_(p_i))`, and the
  class-`k` neighbours of a class-`j` point `P` lie on the single line
  `pi_P cap p_k^perp` of the plane of `P`.  The `B_2` collapse used the
  LINEARITY of `P |-> P^perp`; here the plane map `Q |-> pi_Q` is the
  twisted (octonionic) `G_2` map, not linear, so the two-step sets
  `union_(Q) (pi_Q cap p_j^perp)` over the `q+1` points `Q` of one
  such line should sweep a two-parameter family rather than collapse
  onto one line.  The remaining verification is this spread (or, if it
  fails, the three-class analogue) in Zorn-matrix coordinates, plus
  the point-panel dual; nothing else stands between the recorded cases
  and `(TLS1)` in full.
- **`G_2`: no `B_2`-type collapse — two-step sets are cones
  (2026-08-23, coordinate-free).**  For a class-`j` point `P` of the
  hexagon: the class-`k` neighbour candidates form the line
  `m_P = pi_P cap p_k^perp` of the singular plane `pi_P`, which does
  NOT pass through `P` (`P` is opposite `p_k`, not perpendicular) and
  hence is not a hexagon line (those form the pencil through `P`), so
  it meets each hexagon line through `P` once -- consistent with the
  one-gate-per-line count.  For distinct `Q, Q' in m_P`: they are at
  hexagon distance four with UNIQUE midpoint `P`, so
  `pi_Q cap pi_(Q') = {P}`: the planes `pi_Q` form a pencil of planes
  meeting pairwise only at `P`.  Since `P` is perpendicular to `p_j`,
  `P` lies on every return line `pi_Q cap p_j^perp`; therefore the
  two-step class-`j` reachable set from `P` is a CONE of `q+1`
  distinct lines through `P` in distinct planes -- about `q^2` points,
  against the single line (`q` points) of the `B_2` collapse.  So the
  two-class graph of the hexagon is locally expanding; the remaining
  verification is that iterating the cones (possibly with a third
  class, as in `B_2`) reaches all `~q^4` class-`j` points, e.g. by an
  orbit count for the stabilizer of `(ell_1, p_j, p_k)` in `G_2(q)`.
- **Torsor reduction: the remaining cell is a linear span in the
  parabolic radical (2026-08-23).**  Let `U` be the unipotent radical
  of the line-stabilizer of `ell_1` in the residue's group of Lie
  type; `U` fixes `ell_1` pointwise, so it preserves each class, and
  it acts transitively on the class set `V_j` with stabilizer of order
  `q`: for `B_2` line-panels `U` is the abelian Siegel radical `q^3`
  and `V_j` is a torsor over `F_q^2`; for `B_2` point-panels `U` is
  the Klingen-type `q^(1+2)` with the same `F_q^2` quotient; for `G_2`
  line-panels `U` is the special `q^(1+4)` (the beta-node radical --
  hexagon points are the singular points of the 7-dimensional
  representation, so the alpha-node parabolic stabilizes a point and
  the beta-node one a line) and `V_j` is a torsor over
  `U/Z ~ F_q^4` (`|V_j| = q^4`); for `G_2` point-panels `U` is the
  class-three `q^(2+3)` radical, whose Frattini quotient is only
  `F_q^2`, making that case need just two independent directions.
  The class graphs are `U`-invariant, so their components are cosets
  of the subgroup generated by the two-step translation set, and since
  `U` is special (`Phi(U)=Z(U)`), connectivity is EQUIVALENT to the
  cone translation directions spanning the Frattini quotient
  `U/Z ~ F_q^(rank)`.  VALIDATION on `B_2`: the two-class cone is one
  line, its directions span a 1-space of `F_q^2`, components are the
  `q^2`-order preimage's orbits of size `q` per side -- exactly the `q`
  disjoint `K_(q,q)` found symplectically -- and the third class adds
  the second dimension, reproving the pencil result.  For `G_2` the
  question is whether the `q+1` cone lines (toward class `k`) plus
  their class-`l` analogues span `F_q^4`; the pairwise-distinct planes
  `pi_Q` make a degenerate span of dimension `< 2` per cone
  impossible, so two intermediate classes give at least two
  dimensions, and at most three intermediate classes are plausibly
  needed.  This is now a Chevalley root-subgroup computation in the
  radical `X_beta X_(beta+alpha) X_(beta+2alpha) X_(beta+3alpha)`
  (center `X_(2beta+3alpha)`), with the usual care about structure
  constants in characteristics two and three.
