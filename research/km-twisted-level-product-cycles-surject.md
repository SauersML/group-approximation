---
rg: 2
id: km-twisted-level-product-cycles-surject
kind: claim
title: At every twisted level of the (2,4,6) codistance filtration the product graph cycles surject onto the matched local cycle spaces
distinct_from:
  km-codistance-filtration-twisted-levels-are-rank-two-pairs: that is the established structure theorem reducing the second homology of the development to this statement; this is the remaining finite combinatorial input.
  km-development-has-nonzero-end-cohomology-in-degree-one: that is the end-cohomology input for Corollary D; this is the finite combinatorial statement that makes the thick part 2-connected (type `F_3`) and identifies that input with `H^2_c` of the thick part, without deciding it.
---

**OPEN (finite; scope corrected 2026-08-23: assert only for `q` large
and coprime to six -- for `q=2` the `G_2` case is FALSE, see the
computational bullet).**  For each twisted type of
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
- **`G_2` line-panel sphere equation (2026-08-23).**  In the twelve-gon
  apartment (lines even, points odd, `ell_1` at zero), take the base
  class point `P_0` at position five, foot at position one.  The wall
  dictionary gives: `X_(3alpha+beta)` is the stabilizer of `P_0` in the
  radical, `X_(2alpha+beta)` slides along the geodesic line (staying in
  the class), `X_beta` and the center move to distance four, and
  `X_(alpha+beta)` to distance six.  Writing translations as
  `x_beta(b) x_(alpha+beta)(c) x_(2alpha+beta)(d) x_Z(f)` and using
  that hexagon-distance `<= 4` between points equals perpendicularity
  in the seven-dimensional representation, the coefficient of
  `e_(alpha+beta)` in `u e_(-alpha-beta)` computes the distance sphere:

      `distance(u P_0, P_0) <= 4   iff   c_4 c^2 + c_2 c_7 b d = 0`,

  with `c_7 = N_(beta,alpha) = ±1`, `c_2 = N_(2alpha+beta,-alpha-beta)
  = ±2`, and `c_4` the divided-power double-step constant.  For odd
  `q` prime to three this is a nondegenerate quadric `c^2 = lambda bd`:
  it contains the `b`-axis, the `d`-axis, and curved points with
  `c != 0`, so the distance-four translations span the Frattini
  quotient together with the stabilizer direction.  Validity of
  midpoints: the only distance-three neighbour of `P_0` is the single
  apartment point on the geodesic line, because every `A`-line is
  opposite `ell_1` and so carries only distance-five points; hence the
  invalid (line-four-midpoint or intra-class) part of the sphere is a
  proper positive-proportion subset, the pure `x_beta` moves have their
  midpoint at apartment position seven with foot the OTHER apartment
  class and connecting line `ell_1^op` (valid), and generic curved
  sphere points with `d != 0` retain valid midpoints.  Remaining rigor
  gaps: (i) exhibit two curved valid sphere points independent of the
  `b`-axis (a genericity count over the midpoint-class function), and
  (ii) CHARACTERISTIC 2 AND 3: `c_2 = ±2` kills the `bd` term in
  characteristic two (where also `G_2 <= Sp_6`), and the char-3
  special isogeny changes the radical's center, so even `q` and
  `q = 3^k` need separate sphere computations -- TLS1 could genuinely
  differ there.  The point-panel dual (class-three radical, Frattini
  quotient `F_q^2`) remains to be run through the same dictionary.
- **Point-panel cases by the same wall dictionary (2026-08-23).**  For
  `G_2` point-panels (radical `q^(2+3)`, Frattini quotient the
  `{alpha, alpha+beta}` plane): the stabilizer of the base class line
  is `X_alpha`, and the pure `x_(alpha+beta)` translation is already a
  valid two-step cone move (its midline sits at apartment position
  seven with foot the other apartment class, met through the opposite
  point), so stabilizer plus one visible translation span the Frattini
  quotient: connected for `q` prime to three, two intermediate classes
  suffice.  For `B_2` point-panels (Klingen `q^(1+2)`): the stabilizer
  is `X_(alpha+beta)`, `X_alpha` gives within-class distance-four
  moves, and among the `q+1` transversals of such a pair the apartment
  one fails validity (one meeting point collinear with `p_1`) while
  generic off-apartment transversals are valid, giving the missing
  `alpha` direction: connected.  NET STATUS of `(TLS1)`: grid levels
  proved; `B_2` line-panels proved via the symplectic model; `B_2`
  point-panels, `G_2` point-panels and `G_2` line-panels reduced to
  short genericity counts (exhibiting two independent valid sphere or
  transversal points), all for `q` COPRIME TO SIX; characteristics two
  and three are genuinely open (degenerate structure constants,
  `G_2 <= Sp_6` in characteristic two, the special isogeny in three).
  Since the Kac--Moody candidate class is all `q > 1764^3`, it is
  legitimate to scope the whole `F_3`/Corollary-D-death chain to
  lattices with `q` coprime to six.
- **The invalid part of the `G_2` sphere is a `1/q`-fraction
  (2026-08-23).**  A within-class distance-four pair cannot have its
  midpoint at a CLASS point of the geodesic line: if `P'` is collinear
  with `x_d(t)P_0` then `x_d(-t)P'` is a class-`j_0` point collinear
  with `P_0`, and the only such points are the geodesic slides (each
  `A`-line meets the class only at `P_0` itself), forcing `P'` onto the
  geodesic line and distance two.  So the only invalid midpoints are at
  the single distance-three gate point, contributing `~q^2` of the
  `~q^3` sphere.  Together with `c_4 = ±1` (spin-one string), the
  sphere is `c^2 = ±2bd` and the valid part is all but a
  `O(1/q)`-fraction: three independent valid directions exist for all
  large `q` prime to six, and the remaining bookkeeping is (i) fibering
  the sphere by midpoint class so the two cycle constructions can use
  disjoint (or triangularly ordered) class sets, and (ii) the
  characteristic-two degeneration `c^2 = 0`, which really does collapse
  the two-step locus onto the subgroup `{c=0}` and makes even-`q`
  behaviour a separate question.
- **Characteristic two: the collapse is PROVED (2026-08-23).**  For
  even `q` the hexagon lives on the symplectic `V_6 = V_7/<e_0>` and
  perpendicularity there still detects hexagon-distance `<= 4`.
  Redoing the coefficient computation in the integral Chevalley lattice
  and reducing: the `bd`-path dies (`N_(2alpha+beta,-alpha-beta) = ±2
  = 0`), while the double `alpha+beta`-step survives the quotient by
  the radical (`x_c(c) e_(-alpha-beta) = e_(-alpha-beta) + c N e_0 +
  c^2 c_4 e_(alpha+beta)` with `c_4 = ±1`), and no new paths appear.
  Hence the distance-`<= 4` translation locus is EXACTLY the subgroup
  `{c = 0}` of order `q^4`, every multi-step class walk stays inside
  one `q^3`-orbit, and the class graphs of the `G_2` line-panel levels
  are disconnected for EVERY choice of intermediate classes.  The
  constrained-cycle mechanism therefore provably fails for even `q`;
  whether `(TLS1)` itself fails there (cycles are free to visit points
  of arbitrary classes, so surjectivity is not yet refuted) is open,
  and with it the whole even-`q` branch of the chain.  The odd/even
  dichotomy at `G_2` levels is thus a genuine phenomenon, not an
  artifact of the method.
- **Rational vs integral split (2026-08-23).**  The downward induction
  killing `H^3_c` of the cusp region uses only
  `H^3(level) = Hom(H_3(cl O_w, D), Z)`, which vanishes as soon as
  `H_3(cl O_w, D)` is TORSION.  So the RATIONAL form of `(TLS1)` --
  vanishing of the cokernel after tensoring with `Q` -- already gives
  `H^2(Lambda; Z Lambda) = 0` and the death of Ioana--Spaas--Wiersma
  Corollary D, while the INTEGRAL form is needed only for
  `H_2(X^) = 0`, i.e. for the 2-connectivity of the thick part and the
  type `F_3` conclusion.  The genericity counts at the `B_2`/`G_2`
  levels are naturally rational statements, so the LP-side consequence
  is the more robust of the two.
- **Duality reduction: surjectivity follows from one-class-deleted
  connectivity (2026-08-23).**  A cycle of `A` is determined by its
  point-local data, so `Z_1(A)` is exactly the tuples of zero-sum local
  vectors satisfying one linear condition per line.  Dualizing, an
  annihilator of the image decomposes as `sum_l lambda_l (x) G_l +
  sum_(l'') H_(l'') (x) lambda'_(l'')` over line functionals; evaluating
  at different-class slots and using that every line meets every class
  once, the coefficients `gamma(l,l'',p'') + eta(l'',l,p)` reduce to
  pure gauge whenever the differences `G_l(p'') - G_(l_2)(p'')` can be
  forced into the local span -- which needs exactly that any two lines
  through points of classes other than a fixed one are connected in the
  incidence graph of the opposition geometry with that class deleted.
  A three-point interpolation through different-class witnesses then
  kills every same-class slot: the cokernel vanishes.  So `(TLS1)` at a
  twisted level is implied by: for each class `m`, the graph on
  (single-class vertices of classes `!= m`) and (lines of `A`) is
  connected.  This removes the disjoint-class-set bookkeeping and most
  of the genericity counting; for odd `q` the sphere span gives it away
  from the deleted class, leaving only the midpoint-class distribution
  detail.
- **Characteristic-two cross-check (2026-08-23).**  The proved even-`q`
  collapse says every point-line-point walk translation lies in the
  NORMAL subgroup `{c=0}` (normality: the only nontrivial commutator
  from conjugating its generators lands in the center), so the FULL
  incidence graph of the opposite-line geometry `Gamma(ell_1)` of
  `H(q)`, `q` even, would be disconnected with components in
  `q^3`-blocks.  This is a finite, checkable statement -- for `H(2)`:
  48 points, 32 lines, predicted components of at most 24 points --
  and it either matches a known small-parameter exception list for
  opposition geometries of Moufang hexagons (Abramenko--Van Maldeghem
  treat flag-opposition; the single-element case for even `q` must be
  checked against the literature or by direct computation on MSI), or
  it locates an error in the `V_6` reduction (the candidate weak
  points: the identification of the line parabolic, the wall
  dictionary, and the surviving `c^2`-term in the quotient by the
  radical -- each has been double-checked once).  Deciding `H(2)` is
  the sharpest next test of the whole even-`q` branch.
- **Computational adjudication (2026-08-23, scripts in experiments/,
  artifact km-opposition-connectivity-computations-2026-08-23.md).**
  `H(2)`: the full opposite-line geometry is DISCONNECTED (two
  24-point components) -- the characteristic-two collapse is CONFIRMED
  -- and `b_1(A)^2 = 324 < 768` = target: `(TLS1)` is FALSE at `G_2`
  levels for `q=2` by dimension count.  `H(3)`: the full geometry is
  connected, but deleting any one class disconnects it into three
  81-point components, so every class-restricted cycle mechanism
  (pencil, duality reduction) fails for hexagons even at odd `q`; the
  odd-`q` `G_2` cell is a genuine open RANK computation
  (`~165k x 105k` sparse at `q=3`; dimensionally source `~q^12`
  exceeds target `~q^11` for large `q`, so surjectivity remains
  plausible).  `W(3)`: two-class graphs are exactly `q` disjoint
  `K_(q,q)` and three classes connect -- both symplectic theorems
  validated -- with rank 1272 of 1296 mod two, five and seven
  (experiments/km_w3_rank_modp.py: a genuinely RATIONAL 24-dimensional
  cokernel at `q = 3`, so small-`q` `B_2` levels also obstruct and all
  surjectivity claims are large-`q` statements), consistent with the
  `q+1 >= 7` threshold and warning of small-`q` torsion.  NET: the
  claim as stated must be scoped to ODD `q` (indeed `q` coprime to
  six) and LARGE `q`; for even `q` its negation holds at `G_2` levels
  and the filtration then has genuine relative `H_3` there, reopening
  the connecting-map question and with it the LP fork specifically for
  characteristic-two lattices.  The G_2-level rank computation at
  `q in {3,5}` on MSI is the sharpest next step.
- **Suggested route for the odd-`q` `G_2` rank computation.**  Either
  run the raw sparse rank of the product-cycle map for `H(3)` (about
  `165k x 105k` over a prime other than two and three; LinBox-sized,
  an MSI job), or first apply the annihilator reduction: by the
  different-class-slot analysis the line unknowns `G_l(p'')` are
  constant modulo the local span on each component of the
  `class(p'')`-deleted graph (three components, computed), which
  shrinks the dual system to a few thousand structured unknowns --
  small enough to solve locally IF the gauge bookkeeping (the
  span-valued parts feeding back into same-class slots) is first
  written out carefully; a wrong reduction silently flips the verdict,
  so the raw rank should confirm any reduced answer at `q=3` once.
- **REFUTATION at hexagon levels, all computed q (2026-08-23, later
  same day).**  The one-class-deleted disconnection yields an explicit
  integral annihilator: fix for each class `m` a component `c_0(m)` of
  the `m`-deleted opposition geometry and a nonzero
  `xi(p'') in Z_0(N p'')^*`, and set
  `G_l(p'') = [comp_(class p'')(l) = c_0] xi(p'')`, `H = 0`.  At a
  different-class slot the lines through `p` all lie in the component
  of `p` (they are incident to it), so the sum collapses against the
  relation `sum_l e_l^* = 0` and vanishes; at a same-class slot the
  deleted-class point `p` has its lines distributed over components --
  and full-graph connectivity forces SOME deleted-class point to
  bridge, since otherwise deletion could not disconnect -- giving a
  single surviving term, nonzero.  Hence the cokernel is nonzero over
  `Q` (and `Z`) at every `(G_2, G_2)` twisted level whose one-deleted
  geometry is disconnected: verified for `q = 3` (components
  `[81,81,81]`) and `q = 2`, and structurally expected for all `q`
  (the deletion drops one Frattini direction).  By the same criterion
  the `B_2` and grid levels survive (their one-deleted graphs are
  connected, verified at `q = 3`).  NET: `(TLS1)` as stated is FALSE
  for every `q`; the correct statement of what holds is
  per-level (grid and `B_2` levels: cokernel zero for large `q` prime
  to six; `G_2` levels: cokernel NONZERO with the explicit component
  annihilators).  Consequently `H_3(Z_(<=R+1), Z_(<=R)) != 0` at every
  hexagon level, the downward induction of
  `km-cusp-region-has-degree-three-compact-cohomology` does NOT run,
  and both the `F_3` conclusion and the vanishing of
  `H^2(Lambda;Z Lambda)` return to OPEN, now with explicit relative
  classes whose connecting maps are the decisive objects -- candidate
  SOURCES for `H^2(Lambda;Z Lambda) != 0` and Corollary D, in every
  characteristic.
