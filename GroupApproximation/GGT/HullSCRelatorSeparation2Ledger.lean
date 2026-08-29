import GroupApproximation.GGT.HullSCRelatorSeparation2NoCommute

/-!
# The two-subgroup relator chain: what it rests on

A reader's map of `GGT/HullSCRelatorSeparation2*.lean`, written so that the
manuscript's debt file can cite one place for the chain's standing hypotheses
rather than tracing them through fifty modules.  Nothing is proved here.

## What the chain delivers

`HullSC.HullTheorem51Statement₂` -- Hull's Theorem 5.1 over two hyperbolically
embedded subgroups -- from the corrected separation, `HullConeOffStatement₂`,
and DGO's Theorem 5.3.  The relator is `relatorWord₂`: a base spelling of `t⁻¹`
followed by an alternating run of deep powers of two independent loxodromics.

## The standing hypotheses, and who owes them

**1. The isolated-component bound, in the six-sided form.**  `hgeo` and
`hgeoInv` -- that a short conjugation carrying one deep power onto another
leaves both conjugators in the subgroup -- are no longer hypotheses of this
chain.  They reduce to fp-geometry's bound, through
`GGT.OsinComponents.mem_fam_of_conj_of_deep_six` and
`HullSC.exists_hgeo_of_bound`.  The bound is taken in the six-sided form
throughout -- one spelling, the one `GGT/DGOIsolatedComponentCut.lean` states:
for polygons of at most six sides, an isolated component's span lies in
`relBall lam (C · n)`.  The unrestricted `IsolatedComponentBound` over every
number of sides is not used and is not going to be proved.

  **Proved at `(mu, b) = (1, 0)`, owed at `b > 0`.**  fp-geometry's
  `GGT.OsinComponents.isolatedComponentBound_of_fourPointHyperbolic` proves the
  six-sided statement outright for `IsQuasiGeodesicPolygon D 1 0 n v u`, from a
  symmetric base and four-point hyperbolicity alone, at radius
  `15 · (25 · (δ + 1)) · n`.  This chain's quadrilateral is
  `(1, |p| + c)`-quasi-geodesic and not `(1, 0)`, so the binder still stands
  HERE, at this `(mu, b)`.  Two things would close it and neither is resolved
  in this file: the base case at general `(mu, b)`, which is what dgo-cycle is
  costing, or re-cutting the quadrilateral's sides to geodesics, which changes
  what item 2 has to supply.

**2. `hcount` -- the block count, CYCLICALLY.**  That the distance between two
vertices of the relator is at least the number of block letters between them,
less a constant fixed before the relator is chosen -- asserted not of the
relator alone but of **every prefix of every rotation of it**, which is how
Olshanskii uses it.  Consumed through
`HullSC.quasiGeodesic_relatorWord₂_of_blockCount`, which is what makes the
relator `(1, |p| + c)`-quasi-geodesic.  Open, and genuinely geometric: the
four-gon material consumes quasi-geodesicity rather than producing it.

  **Why the cyclic form, and not the linear one.**  The quadrilateral's two
  long sides are prefixes of rotations, and below the wrap that costs nothing:
  `GGT.OsinComponents.vertex_rotate_prefix` shows a vertex of `w.rotate c` at
  offset `x ≤ |w| - c` to be `(listVal (w.take c))⁻¹ · vertex 1 w (c + x)`, a
  left translate of a vertex of `w`, and `wordDist` is left-invariant, so every
  metric clause about the relator's own vertices transports unchanged on that
  range.  Past the wrap it does not: the continuation is translated by
  `listVal R = t⁻¹u`, which is not `1` -- the relator is not a closed word, and
  two indices on opposite sides of the seam are `d(v_{c+x}, listVal R · v_y)`
  apart, which no clause about `R`'s own vertices controls.  That is the whole
  difference from the quadrilateral, whose `listVal` IS `1`.  The wrapping half
  is exactly what the cyclic form supplies; it is not to be derived from the
  linear form together with the depth clause.

**3. The two same-side exclusions.**  That no two distinct components of one
long side of the quadrilateral are connected to each other, one clause per
side.  This is what replaces the old item 3 -- "a long match produces matched
blocks with both gaps short" -- which is now proved rather than assumed
(`GGT.OsinComponents.two_block_conj_named`, with its two configuration clauses
discharged by `GGT.OsinComponents.innermost_of_sideExclusions` and
`otherArc_of_sideExclusions`, composed in
`GGT.OsinComponents.exists_eps_matchedPair`).

  The exclusions are not a new debt.  They come in two halves, and only the
  second is owed: the geometry bounds how far apart two connected components of
  one side can be -- `HullSC.index_close_of_connected` gives `i' - i ≤ 1 + b`,
  the connector being one letter of the alphabet and the side quasi-geodesic --
  and the design excludes connections within that range, which is
  `HullSC.exists_separated_exponents_window` at `W := 1 + |p| + c`, a window
  fixed before the exponent list because `b` is.  The geodesic route,
  `GGT.OsinComponents.not_connected_qBlock_of_isComp`, reads `distance ≤ 1` off
  as `|i - i'| ≤ 1` and needs the side GEODESIC; the sides here are not, which
  is why the design carries this and not the geometry.

**4. `HullConeOffStatement₂` and `DGOQuotientStatementGeodesic`.**  Citations:
Hull's §5, that the cone-off along a pair exists with the data
`HullSC.ConeOffData₂` records; and DGO's Theorem 5.3 in the repaired form that
carries a geodesic, `GGT/HullSCDGO.lean` having refuted the transcribed one.

**5. Torsion-freeness.**  A hypothesis about the groups the manuscript studies,
not a leaf, and the chain's only use of it is
`HullSC.noCommute_of_torsionFree`.

## The composition's binders

The separation's match clause, threaded through the modules below, keeps
exactly these and no others:

* `hbound` -- item 1, at this chain's `(mu, b)`;
* `hqg` -- item 2, as the `fourGonCut` clause for
  `py ++ u₀ ++ pz ++ revWord u₀'`;
* the two same-side exclusions -- item 3;
* `0 < |py|` and `0 < |pz|` -- the piece side conditions.

`Connected` at the matched pair and both configuration clauses of the packaged
theorem were binders and are not any longer: the first comes from
`GGT.OsinComponents.exists_other_component_of_deep_six`, the other two from
item 3.

## The construction's named clauses

Three choices the construction has to make in this order, and the argument is
unsound without them.

* **(C1) The base part is fixed first.**  `p` is chosen once, before `B`, at
  length at least one, and does NOT grow with the requested run length `L`.
  `HullSC.exists_long_base_spelling₂` at `P := 1` supplies it.  A construction
  that lengthened `p` with `L` could be handed a piece lying wholly inside the
  base arc, where `HullSC.exists_block_of_long_prefix_rotate` has nothing to
  say -- a window of more than `|p|` letters meets the run, and a shorter one
  need not.
* **(C2) The piece threshold.**  `B := |p| + 2(eps + 1) + 2`, which is what
  puts two block letters in every piece, separated by more than `2(eps + 1)` --
  the separation `GGT.OsinComponents.exists_two_block_connector_of_deep` asks
  for, and what the mixed cases need in order to see an orientation at all.
* **(C3) The run is long.**  `L` past `2(2(eps + 1) + 1) + |p| + c + 2`, which
  is what `HullSC.false_of_span_mixed`'s length clause
  `2(i₂ - i₁) + gapSlack < |R|` becomes once the two blocks are chosen at
  `i₂ := i₁ + 2(eps + 1) + 1` and `gapSlack := |p| + c + 2`.  Free: `|R|` is
  `|p| + |ms|` and `|ms|` is whatever `L` asks for.

The two side conditions `0 < |py|`, `0 < |pz|` are met by padding the
connectors' base spellings with a letter and its inverse
(`HullSC.exists_long_base_spelling_of_base_eq` at `P := 1`, applied to `y⁻¹`
and `z⁻¹`).  Padding changes neither what the spelling names nor its word norm,
and nothing downstream reads the LENGTH of a short side -- the pinning estimate
reads `wordNorm (listVal p) ≤ eps` -- so the degenerate branches `y = 1` and
`z = 1` need no separate treatment.  Recorded as a clause of the construction
rather than as a proved step: the composition that spends it is not yet
written.

## What is discharged, and by what

* The diagonal of the separation -- no short pair carries a deep power onto
  itself -- from torsion-freeness, `HullSC.noCommute_of_torsionFree` over
  `GGT/OsinTheorem54SepElementaryBall.lean`.  It holds for every loxodromic;
  nothing has to be chosen.
* The rigidity input, from the bound: `HullSC.exists_hgeo_of_bound`.  Its
  degenerate branch needs no geometry -- with the second conjugator trivial,
  `x · a^i · 1 = a^j` gives `x = a^j (a^i)⁻¹`, a product of peripheral
  elements -- and the norm bounds on the conjugators are not used at all:
  the reduction wants them base-spelled, and shortness enters only through the
  quadrilateral's quasi-geodesicity.
* Both gaps of a matched pair, BY NAME, in a relative ball whose radius is
  fixed before the data: `GGT.OsinComponents.two_block_conj_named`, composed
  with the two configuration clauses in
  `GGT.OsinComponents.exists_eps_matchedPair`.  The naming is what the aligned
  branch spends -- the join consumes the vertex relation, which is what the
  first gap being trivial SAYS once the gap is known to be
  `(vertex 1 s j)⁻¹ · (listVal p · vertex 1 q i)`.
* That a piece longer than `|p|` carries a block letter, direct and mirrored:
  `HullSC.exists_block_of_long_prefix_rotate` and `..._revInv`.
* That the block letter is a component of the matched prefix:
  `HullSC.isComp_prefix_rotate_relatorWord₂` and `..._revInv_...`.  Neither
  passage is free -- under a rotation the neighbour of the first block letter
  is the relator's last, and `0 < |p|` is what excludes the wrap on both sides.
* The same-side exclusion at adjacent components, from a deep power not lying
  in the other subgroup: `HullSC.notMem_fam_of_crossDeep`.
* The mixed cases' gap estimate: `GGT.OsinComponents.wordDist_match_le` (the
  short side cancels between two matches, so the matched pair is at most two
  further apart, with no `eps` in it) and `le_of_qg_one` (the quasi-geodesic
  clause at `mu = 1`, in naturals).  At `mu > 1` the estimate is multiplicative
  and the additive shape `HullSC.false_of_span_mixed` wants is not available,
  which is why the block-count route is the one that has to be taken.
* All four cases of step (c): `HullSC.listVal_conj_of_alignedMatch_pair` and
  `HullSC.listVal_conj_of_mirroredAlignedMatch_pair` for the aligned ones,
  `HullSC.false_of_span_mixed` and `HullSC.false_of_mixedMatch_gap_inv` for the
  two mixed orders, dispatched by `HullSC.listVal_conj_of_sym_cases`.
* `0 < |p|`, which the wrap-around argument of
  `GGT/HullSCRelatorSeparation2Locate.lean` spends, from
  `HullSC.exists_long_base_spelling₂`.

## Four refutations that shaped the chain

They are recorded because each closed a route that looks reasonable on paper.

* `HullSC.RelatorSeparation` as transcribed is FALSE: it quantifies over the
  diagonal `w' = w`, and a conjugator inverting the loxodromic refutes it
  (`GGT/HullSCRelatorSeparationRefuted.lean`).  The repair restores Olshanskii's
  exclusion clause `w' ≠ w`.
* The single-subgroup relator is not quasi-geodesic: its run is one component,
  and the defect grows with the exponents
  (`GGT/HullSCRelatorSeparationNotQG.lean`).  That is why the model has two
  subgroups and an alternating run, and it is also why the relator is aperiodic
  (`GGT/HullSCRelatorSeparation2Aperiodic.lean`).
* The four-gon's closing clause `r = p⁻¹` is FALSE
  (`fourGon_closing_clause_fails`), and equivalent to a centralizer claim about
  the piece's own connector -- the equivalence is
  `HullSC.conj_rotate_iff`.  The aligned case does not need it: the vertex form
  pins the connector to the four-gon's own first side, which is
  `HullSC.listVal_conj_of_rotate_eq_of_vertex_eq`.
* Lemma 4.21 in the start-to-start form is FALSE; only the innermost
  end-to-start element is bounded.  The rigidity consumes exactly two such, one
  per orientation of the boundary.

## One correction worth keeping

The existential form of the packaged polygon theorem loses exactly what the
aligned branch needs.  From `∃ x x', x · v_q · x' = v_s` the design still forces
`x = 1` and `x' = 1`, so it still forces `e = f`; but `x` is then an anonymous
element of the ball, and the vertex relation the join consumes does not follow.
The named form is not a convenience.
-/
