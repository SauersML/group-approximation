# Opposition-geometry computations for the twisted-level surjectivity (2026-08-23)

Scripts: experiments/km_h2_opposition_connectivity.py,
km_h3_opposition_connectivity.py, km_w3_class_graphs_and_rank.py
(sub-second builds of `H(2)`, `H(3)`, `W(3)` from the quadric/symplectic
models, with built-in verification: point/line counts, `q+1` lines per
point, girth at least twelve, one point per class on every opposite
line).  The split Cayley hexagons were cut out of the quadric lines by
the classical Plücker conditions
`p01=p36, p12=p34, p20=p35, p45=p23, p56=p03, p64=p13`
(sign search at `q=3` landed on `(1,1,1,-1,-1,-1)`).

Results, for a fixed line `ell_1`, far points classed by their foot:

- `H(2)`: 48 far points (16 per class), 32 opposite lines.  The FULL
  opposite-line geometry is DISCONNECTED: two components of 24 points.
  This CONFIRMS the characteristic-two collapse predicted by the
  `V_6` Chevalley computation (components = `q^3`-blocks), and with
  `b_1(A) = 18` the product-cycle map has source `18^2 = 324` against
  target `768`: the twisted surjectivity `(TLS1)` is FALSE at `G_2`
  levels for `q = 2` by dimension count alone.
- `H(3)`: 324 far points (81 per class), 243 opposite lines; girth
  check passes.  The FULL geometry is CONNECTED (odd-`q` sphere
  argument validated), but deleting ANY single class disconnects the
  rest into three components of 81: every class-restricted cycle
  mechanism fails for hexagons even at odd `q`.  Odd-`q` `(TLS1)` at
  `G_2` levels is therefore an open finite rank computation
  (`164836 x 104976` sparse at `q=3` -- an MSI job), not a corollary of
  connectivity arguments.
- `W(3)`: two-class graphs = three components of six points = `q`
  disjoint `K_(q,q)` -- exactly the symplectic perp-collapse theorem;
  three-class graph connected -- the pencil rescue confirmed.  The
  mod-two rank of the product-cycle map is 1272 of 1296: consistent
  with the disjoint-class proof needing `q+1 >= 7`, and a warning that
  small-`q` levels can carry genuine (at least torsion) cokernel.

Addendum (same day): the `H(3)` deleted-class pieces are `(81
points, 81 lines)` each and EVERY deleted-class point is transversal --
its three lines hit all three pieces, profile `(1,1,1)` for all 81
points -- confirming the index-`q` grading predicted by the torsor
analysis and making the component-indicator annihilator nonzero at
every matched slot (`km-hexagon-level-cokernel-is-nonzero`).

Addendum 2 (same day): the opposite lines of `H(3)` form a simply
transitive torsor under the `q^5` radical, and the four class-gradings
(piece index after deleting each class) are JOINTLY SURJECTIVE onto
`(Z/3)^4` with fibers of size three -- pairwise independent (nine
blocks of 27), triple-wise (27 of 9), quadruple-wise (81 of 3).  The
class gradings thus canonically realize the full Frattini quotient
`U/Phi = F_q^4` of the line-parabolic radical, one coordinate per
panel class; for `q > 3` the `q+1` gradings must satisfy `q-3`
relations.  This is the combinatorial skeleton any connecting-map
computation will use.

Addendum 3 (same day, experiments/km_w3_omega_h2_validation.py): at
the `W(3)` twisted level the reduced simplicial `H_2(Omega; F_2)`,
computed from raw boundary ranks (`d_3` rank 7904 of 8748, `d_2` rank
3736 of 11664), equals 24 -- EXACTLY the cokernel dimension
`1296 - 1272` of the product-cycle map computed by the independent
graph-cycle code path.  The Mayer--Vietoris/cokernel identification of
the level complexes (`km-codistance-filtration-twisted-levels-are-rank-
two-pairs` (d)) is thus numerically confirmed at a nontrivial
instance.

Addendum 4 (same day, experiments/km_h2_omega_h2_validation.py): the
same two-path validation at the `H(2)` (disconnected) level, after
fixing a coordinatization bug (difference coordinates on zero-sum
vectors degenerate mod two exactly for even `q`; they are an
isomorphism at `q = 3`, so the `W(3)` numbers stand): the product-cycle
map has rank 320 mod two, and the simplicial `H_2(Omega;F_2) = 484`
equals the disconnected-case prediction `(768 - 320) + 2 b_1 = 448 +
36` exactly.  Both regimes of the level-complex formula are now
confirmed by independent code paths.

Net effect on the chain: the conditional results (type `F_3`,
`H^2(Lambda;Z Lambda) = 0`, death of Ioana--Spaas--Wiersma Corollary D)
now rest on an OPEN rank computation at the odd-`q` `G_2` levels, and
are genuinely FALSE-hypothesis for even `q`, where the `G_2` levels
carry nonzero relative `H_3` classes and the connecting-map analysis
(hence the LP fork) REOPENS specifically for characteristic-two
Kac--Moody lattices.  The framework itself (wall dictionary, torsor
structure, class counts, collapse prediction) is now triple-validated
against independent computation.
