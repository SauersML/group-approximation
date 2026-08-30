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
followed by an alternating run of deep powers of two loxodromics, one in each
of the two subgroups.  Hull takes them independent; the chain asks only that
the subgroups meet trivially, which is (W4) --- see item 6.

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

  **The mathematics is discharged; a quantifier prefix is not.**  fp-geometry's
  `GGT.DGOPolygonBaseCaseTower.isolatedComponentBound_of_fourPointHyperbolic_at`
  proves the six-sided statement outright for
  `IsQuasiGeodesicPolygon D 1 (b : ℝ) n v u` at every NATURAL `b`, from a
  symmetric base and four-point hyperbolicity alone, at radius
  `15 · (25 · (δ + b + 1)) · n`.  This chain's quadrilateral is
  `(1, |p| + c)`-quasi-geodesic, and `|p| + c` is a natural, so the instance the
  chain actually uses is proved.  Four-point hyperbolicity of `Γ(G, X ⊔ ℋ)`
  takes its place as the standing geometric hypothesis.

  What is not yet discharged is the SHAPE the chain spells the bound in.  The
  binder carried from `GGT/DGOIsolatedComponentCut.lean` down through
  `GGT.OsinComponents.exists_other_component_of_deep_six` is
  `∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C, 0 < C ∧ …` --- universally quantified over
  every REAL pair --- while the tower supplies `mu = 1` and `b` natural.  The
  gap is not mathematical: every consumer along the chain spends the binder at
  exactly ONE pair (`exists_other_component_of_deep_six` at its line 230), and
  the pair this chain picks is `(1, ((|p| + c : ℕ) : ℝ))`.  So the binder
  over-quantifies, and narrowing it to `∃ C, 0 < C ∧ …` at the chain's own pair
  makes the tower discharge it outright.  Supplying the universally quantified
  form INSTEAD is not available: at `mu > 1` the multiplicative defect cannot be
  absorbed into an additive one, and the tower says nothing there.

  **The narrowing is done, and item 1 is closed.**
  `GGT.OsinComponents.exists_other_component_of_deep_six_at` states the
  deep-six step at this chain's own pair, and
  `GGT.OsinComponents.exists_deep_match_hyp` discharges it from four-point
  hyperbolicity outright.  On the gap side
  `GGT.OsinComponents.two_block_conj_of_hyperbolic` proves the two-block
  conjugation from `hδ` at every real `b ≥ 0`, with the passage to `⌈b⌉₊`
  inside it; `GGT.OsinComponents.two_block_conj_named_hyp` is its instance at
  `b := (bn : ℝ)`, the one pair this chain spends, and
  `GGT.OsinComponents.exists_eps_matchedPair_hyp` packages that one.  Both
  producers deliver the interfaces of
  `GGT/HullSCRelatorSeparation2ApplyIface.lean`, so the composition takes `hδ`
  and no longer carries `hbound` at all.

**2. `hcount` -- the block count, CYCLICALLY.**  That the distance between two
vertices of the relator is at least the number of block letters between them,
less a constant fixed before the relator is chosen -- asserted not of the
relator alone but of **every prefix of every rotation of it**, which is how
Olshanskii uses it.  Open, and genuinely geometric: the four-gon material
consumes quasi-geodesicity rather than producing it.

  **The count is now the whole of the debt.**
  `HullSC.separationNe₂_clause_of_inputs` takes `hcount` at every member of the
  symmetrized closure --- `j - i ≤ d(vertexᵢ, vertexⱼ) + blockConst p cnt` ---
  and produces all three clauses the polygon asks:

  * the two per-side clauses, by `HullSC.qgClause_of_le`, the cast from the
    count in naturals to the `mu = 1` clause over the reals, carried to a
    PREFIX of a member by `GGT.OsinComponents.vertex_append_of_le`;
  * the `fourGonCut` clause, by `HullSC.fourGonQG_of_sides`: side one is a left
    translate of `u` and the word metric is left invariant, side three is
    `revWord u'`, whose vertices are `u'`'s reversed and translated
    (`GGT.OsinComponents.vertex_revWord`), and the two short sides are covered
    by their LENGTH, the distance they are compared against being a natural
    number.

  **The constant is not the count's own.**  The two short sides are base
  spellings of the separation's `y` and `z`, and the metric is the relative
  one, in which a short element lying in `H λ` has norm one while its base
  spelling has length `eps`.  No bound below `|py|` can serve there, so the
  composition works at `max cnt (eps + 2)` and not at `cnt`.  It chooses that
  itself --- `eps` is given before anything it chooses, and enlarging the
  constant only weakens the count --- so `cnt` stays a constant of the core.
  The length bound `|py| ≤ eps + 2` is why
  `HullSC.exists_side_spelling_of_base_eq` takes a MINIMAL spelling and pads
  it, rather than taking any spelling at all.

  **Where values enter.**  `HullSC.quasiGeodesic_relatorWord₂_of_blockCount`
  never unfolds the relator and never touches a value: it is arithmetic over
  `j - max i |p|` and an opaque `wordDist`.  So rotation does not break the
  reduction --- it generalises verbatim, with `j - max i |p|` replaced by
  `(j - i) - |p|`, which holds because rotation permutes letters and formal
  inversion carries base letters to base letters, so a member of the closure
  has exactly `|p|` base letters wherever they sit.  What does not transport is
  the DERIVATION of the cyclic count from the linear one:

  the quadrilateral's two long sides are prefixes of rotations, and below the
  wrap that costs nothing:
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

  **Two of its three steps are built, and unconditionally.**  The count is the
  injection of the piece's components into a geodesic's, and only the first of
  its three steps is geometric.  `GGT.OsinComponents.card_le_card_of_crossConnected`
  and `card_le_card_of_sideSeparated`
  (`GGT/HullSCRelatorSeparation2CountBigon.lean`) are steps two and three, over
  arbitrary words: distinct components of the near side reach distinct
  components of the far side, so their number is at most the far side's.  The
  target is a `Finset` the caller supplies rather than the far side's LENGTH,
  and that is what keeps `mu = 1`: bounding each index's count by `|q|` would
  give `k_false + k_true ≤ 2|q|`, the clause at `mu = 2`, whereas the two
  indices land on disjoint sets of component starts
  (`not_isCompStart_of_ne`) and so ADD to at most `|q|`.
  `GGT/HullSCRelatorSeparation2BaseCount.lean` is the arithmetic on the other
  side: `baseCount_of_sym_relatorWord₂` proves the `|p|` this section asserts,
  and `compCount_range_ge` turns a component count into the count above.  What
  is left is step one, that a deep component of the piece is not isolated in
  the figure it makes with the geodesic.

  **No citation reaches that step, and the reason is sharper than a missing
  reference.**  Hull gets quasi-geodesicity of his relator from
  Dahmani--Guirardel--Osin's Lemma 4.21(1), which this repository already reads
  as `(4,1)` (`GGT/DGOCorollary612Unconditional.lean`), and two things stop it
  from discharging the count.

  * The constant is MULTIPLICATIVE.  `(4,1)` bounds a length by four times a
    distance, and `hcount` is `mu = 1` with an additive constant, as is every
    consumer of it --- `HullSC.qgClause_of_le`, `le_of_qg_one`,
    `HullSC.fourGonQG_of_sides`, and item 1's own narrowing, which is at
    `mu = 1` because the tower says nothing above it.  So the citation proves
    something strictly weaker than the chain consumes --- and intrinsically so.
    The bound's radius is `C · n`, linear in the SIDE COUNT
    (`GGT/DGOIsolatedComponentCut.lean`), and 4.21's proof subdivides the path
    into single edges before closing it with a geodesic, so `n` grows with the
    piece and the radius grows with it, while the depth clause is fixed before
    `ms`.  A fixed depth stops beating `C · n`, "every component is
    non-isolated" fails for long pieces, and the multiplicative constant is
    what is left.  No amount of side-count strength removes it.
  * Its condition (W1) reads on LETTERS --- no subword `xy` with both letters
    in `X` --- and this relator opens with `|p|` consecutive base letters.
    (W4) is the sharper form of the same objection: it asks for
    `W ≡ U₁ x U₂` with `U₁, U₂` over `H_α ⊔ H_β` and `x ∈ X ∪ {1}`, so a
    relator with two `X`-letters fails (W4) before it fails (W1), and no
    syllabic reading of (W1) would rescue it.  Hull's word has exactly one:
    he reads it in `(𝒜 ∪ {t^{±1}}) ⊔ ⟨h₁⟩ ⊔ ⟨h₂⟩`, adjoining `t` to the
    alphabet as a LETTER, while this chain spells `t⁻¹` as a word over `𝒜`
    because `t` is arbitrary.  The deviation is in the spelling, not in the
    predicate.

  Both conditions hold, though, on a piece lying INSIDE the run: it has no
  `X`-letters at all, so (W1) is vacuous and (W4) holds with `x = 1`; (W3) is
  local and follows from the run alternating indices; (W2) is the design's
  depth clause at a radius the composition chooses.  So 4.21(1) does reach
  run-internal pieces, and gives them `(4,1)` --- and only them.  A piece
  meeting the base arc has no progress bound from any source, and the
  arithmetic does not compose across the arc: splitting a crossing range and
  adding the two counts bounds it by the SUM of two distances, which is not
  the distance between its endpoints.

  **The base-crossing half may be a defect of the spelling rather than a
  debt.**  Nothing in this chain reads `|p|` except as an upper bound and
  `0 < |p|`: `HullSC.exists_long_base_spelling₂` returns any base spelling of
  `t⁻¹` with `P ≤ |p|` and the composition asks it at `P := 1`.  So if the
  alphabet contained `t⁻¹` the spelling could be `[t⁻¹]`, the relator would
  have one `X`-letter, and 4.21(1) would reach EVERY piece.  What stands in
  the way is not in these files: `HullSC.ExistsHypEmbeddedConeOff₂` cones off
  over `A.alphabet`, where Hull cones off over `𝒜 ∪ {t^{±1}}`, and restating
  the citation over the enlarged alphabet is a change to what it asks of the
  geometry.

  **So item 2 is open because item 1 is closed narrowly, and the two move
  together.**  For a run-internal piece the missing step is the
  isolated-component bound at a two-sided figure with one geodesic side and one
  `(4,1)` side --- that is item 1's bound, at `mu = 4`, where item 1 is
  discharged only at `mu = 1` and `n ≤ 6`.  Listing them as independent debts,
  as this file did, was wrong.  For a base-crossing piece not even that is
  enough, and what would be needed first is either a progress bound on a word
  that is not one of Hull's, or the spelling of `t` above.

**3. The two same-side exclusions.**  That no two distinct components of one
long side of the quadrilateral are connected to each other, one clause per
side.  This is what replaces the old item 3 -- "a long match produces matched
blocks with both gaps short" -- which is now proved rather than assumed
(`GGT.OsinComponents.two_block_conj_named`, with its two configuration clauses
discharged by `GGT.OsinComponents.innermost_of_sideExclusions` and
`otherArc_of_sideExclusions`, composed in
`GGT.OsinComponents.exists_eps_matchedPair`).

  **They carry a component-start clause, and the version without it is FALSE.**
  Quantified over every index `i'` of the side, the exclusion at `i' = i + 1`
  excludes the span of the matched component itself --- the value of a
  `lam`-letter, which lies in `H lam`.  `HullSC.not_sideExclusion_of_isComp`
  derives `False` from it, using only the component and the side's letters,
  both of which the matching step has in hand.  The chain carried that form
  until 2026-08-29 and was vacuous for as long as it did; the defect entered at
  `HullSC.cross_of_notSameSide`, which destructured the same-side disjunct of
  `exists_other_component_of_deep_six` and discarded its `IsCompStart` clause
  before applying the exclusion.  The repaired form is

      ∀ i' ≤ q.length, i' ≠ i →
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') →
          (vertex 1 q i)⁻¹ * vertex 1 q i' ∉ D.fam lam

  which is item 3 as stated in words, and which `i + 1` does not satisfy:
  adjacent letters of one index lie in ONE component.  Both consumers had the
  clause already.

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

  **What the design does not yet reach.**  The window clause excludes
  `a s ^ n * listVal (blockWord h₀ h₁ t (post.take r))` from `D.fam (!s)`, a
  block letter followed by a pure RUN of block letters.  For the same-family
  exclusion the first letter is peeled: if `span(i, i') ∈ H lam` then
  `span(i+1, i') = (a lam ^ n)⁻¹ · span(i, i') ∈ H lam` as well, and that span
  starts at an `!lam`-letter, so the window clause at `s := !lam` excludes it
  from `D.fam (!(!lam)) = D.fam lam`.  That covers every range lying inside the
  run.  It does not cover a range crossing the base arc, which
  `HullSC.index_close_of_connected` leaves within reach --- `1 + |p| + c`
  exceeds `|p|` --- and where the span has `listVal p = t⁻¹` as an interior
  factor.  Closing that needs a through-the-base version of
  `HullSC.exists_separated_exponents_window`: finitely many patterns of block
  letters either side of the base arc, and a finite bad set for each, by the
  same argument the window lemma already runs.

**4. `HullConeOffStatement₂` and `DGOQuotientStatementGeodesic`.**  Citations:
Hull's §5, that the cone-off along a pair exists with the data
`HullSC.ConeOffData₂` records; and DGO's Theorem 5.3 in the repaired form that
carries a geodesic, `GGT/HullSCDGO.lean` having refuted the transcribed one.

**5. Torsion-freeness.**  A hypothesis about the groups the manuscript studies,
not a leaf.  It was carried in order to buy the diagonal clause of item 6; the
chain does not ask for that clause any longer, and torsion-freeness now enters
only where Hull's own derivation of (W4) does.

**6. The diagonal leaf -- CLOSED, and not by proving it.**  The clause was that
no nontrivial element of a relative ball commutes with a positive power of the
loxodromic:

    ∀ e s, ∀ x ∈ relBall s e, x ≠ 1 → ∀ d, 0 < d → ¬ Commute x (lox s ^ d)

and it is not a consequence of torsion-freeness.  Both `x` and the loxodromic
lie in `H λ`, so where `H λ` is abelian --- and `E(g)` in a torsion-free group
is infinite cyclic --- every `x` commutes with every power, and the clause
fails for every nontrivial `x` of the ball.  What it asked is that
`relBall λ eps` meet the centralizer of `lox λ` trivially: a condition on the
CORE, not a property of the ambient group.

  **Hull does not ask it.**  His pieces exclude the conjugacy identity
  syntactically, and what makes the aligned case's connector trivial is (W4),
  `H₀ ∩ H₁ = {1}`, which is now the field
  `HullSC.HypEmbeddedCore₂.disjoint`.  The mechanism is
  `HullSC.trivialGap_of_two_connectors`: at two matches from ADJACENT
  components the second gap of the first and the first gap of the second are
  inverse --- they share the near-side vertex --- so one element lies in both
  subgroups at once, `HullSC.index_alternates_of_rotate` makes the two indices
  opposite, and (W4) kills it.  `HullSC.exists_match_with_trivialGap` and
  `..._revInv` run that at three consecutive block letters and hand the closers
  the equation they used to get from the design.  Three letters and not two
  because the far component of the first match can be the last letter of the
  piece; with three there are two candidate pairs and at most one is spoiled.

  **On the input side it is a theorem, not an assumption.**  At the
  cyclic-reduction interface `HullSC.existsHypEmbeddedConeOff₂_of_zpowers`
  discharges the field outright: the two subgroups there are `⟨h₀⟩` and `⟨h₁⟩`
  for a pair of independent loxodromics, and
  `GGT.Elementary.zpowers_disjoint_of_independent` intersects them trivially.
  Hull's own derivation at general peripheral subgroups --- Corollary 5.7's
  `E(hᵢ) = ⟨hᵢ⟩`, independence, and DGO's 6.8 and 6.14 making `E(h₀) ∩ E(h₁)`
  finite, hence trivial in a torsion-free ambient --- is cited at the field and
  is not in this tree.

## The composition's binders

The separation's match clause, threaded through the modules below, keeps
exactly these and no others:

* `hδ` -- item 1: four-point hyperbolicity of the RELATIVE Cayley graph
  `Γ(G, X ⊔ ℋ)`, which is what the two producers consume and all that is left
  of the bound;
* `hcount` -- item 2, the block count at every member of the symmetrized
  closure.  It used to be spent as three separate clauses; those are now proved
  from it, so what is carried is the count alone;
* the two same-side exclusions -- item 3.

There is no fourth.  The diagonal leaf was carried here until (W4) replaced it;
see item 6.

The design's other clauses -- `hnodup`, `hinj`, `hsep`, `hdeep`, and the
symmetry of the base -- are discharged by the instantiation and are not standing
hypotheses of the finished statement.  `0 < |py|` and `0 < |pz|` were on this
list and are not any longer: see the padding remark below.

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
* **(C2) The piece threshold.**  `B := |p| + 2(eps + 1 + b) + 2`, that is
  `|p| + blockSeparation + 2`, with `b = |p| + c` the block-count constant.
  This is what puts two block letters in every piece separated by more than
  `blockSeparation` -- the separation
  `GGT.OsinComponents.lt_of_two_connectors_qg` asks for, and what the mixed
  cases need in order to see an orientation at all.

  It is a theorem and not an estimate:
  `HullSC.exists_two_blocks_of_long_prefix_rotate` and `..._revInv` produce the
  two offsets from a window of `|p| + blockSeparation + 2` letters, by writing
  them down in three branches according to where the rotation starts.  The
  branch that fixes the constant is the one where the window starts inside the
  run with fewer than `blockSeparation + 1` letters of tail left: it crosses
  the base arc and re-enters the run, and the tail's shortness is what bounds
  the second offset.  The count also returns `d₂ ≤ |p| + blockSeparation + 1`,
  which is what (C3) is read from.  Choosing `d₂ := d₁ + blockSeparation + 1`
  instead of finding it would be unsound -- that position can lie in the base
  arc, where there is no letter to match.

  The `+ b` is not slack.  The geodesic pinning
  `GGT.OsinComponents.index_le_of_connector` would give `2(eps + 1)`, but it
  reads `wordNorm (vertex 1 q i) = i` off the side being geodesic, and these
  sides are only `(1, b)`-quasi-geodesic, where that identity fails in both
  directions.  What survives is
  `GGT.OsinComponents.index_le_of_connector_qg`, the same statement with `b`
  added, and the separation has to be taken against it.  Without an order
  between the two matches the mixed cases cannot be closed at all: one match
  alone is consistent with an inversion, and
  `GGT.OsinComponents.wordDist_match_le` bounds the distance between two
  matches while saying nothing about the sign.
* **(C3) The run is long.**  `L` past `|p| + 5 · blockSeparation + 2`.  The two
  mixed orders ask slightly different things --- the direct one
  `2(d₂ - d₁) + blockSeparation < |R|`, the inverted one
  `2(d₂ - d₁) + 3 · blockSeparation < |R|`, because there the length clause is
  about the MATCHES' indices and each is within `blockSeparation` of its
  source --- and the second implies the first, so one number serves both.  The
  count of (C2) bounds `d₂ - d₁` by `d₂ ≤ |p| + blockSeparation + 1`, and `|R|`
  is `|p| + |ms|`, so the inverted clause follows from
  `|p| + 5 · blockSeparation + 2 < |ms|`.  Free: `|ms|` is whatever `L` asks
  for.  The `|p|` in the threshold is not slack --- it is the length of the
  base arc the window may have to cross to find its second letter.

  The slack is `blockSeparation` in BOTH orders, and not the sharper `b + 2`
  that `GGT.OsinComponents.gap_and_order_of_two_matches` returns, because that
  lemma asks both connectors to lie in one `H_λ` and in the mixed case they do
  not: `HullSC.blockWord_index_alternates` makes consecutive block letters carry
  opposite indices, so two blocks share an index exactly when the distance
  between them is even, and `blockSeparation + 1` is odd.  `b₁ = b₂` is
  therefore false here, not merely unproved.  Nothing is lost by it --- the
  common index was never used for anything, both estimates reading a connector
  only through `wordNorm h ≤ 1`, which holds for an element of any `H_λ` --- so
  each match is pinned separately and the gap bounded at both ends.

The two side conditions `0 < |py|`, `0 < |pz|` are met by padding the
connectors' base spellings with a letter and its inverse
(`HullSC.exists_long_base_spelling_of_base_eq` at `P := 1`, applied to `y⁻¹`
and `z⁻¹`).  Padding changes neither what the spelling names nor its word norm,
and nothing downstream reads the LENGTH of a short side -- the pinning estimate
reads `wordNorm (listVal p) ≤ eps` -- so the degenerate branches `y = 1` and
`z = 1` need no separate treatment.  This is a proved step and not a clause:
`HullSC.exists_side_spelling_of_base_eq` returns the padded word with its
letters, its positive length, its value, and its RELATIVE norm, the last by
monotonicity of the word length in the alphabet, and
`HullSC.exists_side_spelling₂` is the form over the two-subgroup core.  What
remains unwritten is only the composition that spends it.

## What is discharged, and by what

* NOT the diagonal of the separation, and it is not asked for.  This entry
  read "from torsion-freeness, `HullSC.noCommute_of_torsionFree`; it holds for
  every loxodromic, nothing has to be chosen", and that is wrong here.  The
  lemma asks its element to be loxodromic in the RELATIVE graph, and the
  relator's letters are powers of `E.lox b`, which `lox_mem` puts inside
  `H b`.  An element of the family is a single letter of the relative alphabet,
  so its orbit of the basepoint has diameter at most one and it is elliptic ---
  which the tree already proved, at the file that defines the relative
  generating set: `GGT.RelGenSet.not_isLoxodromic_of_mem_fam`.  The instance at
  the core is `HullSC.not_isLoxodromic_lox₂`.  The route is closed for every
  group and every core; the clause it was to prove is gone, replaced by (W4)
  --- item 6.
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
  `HullSC.exists_block_of_long_prefix_rotate` and `..._revInv`; that a
  piece longer than `|p| + k + 1` carries TWO of them more than `k` apart, at
  a second offset of at most `|p| + k + 1`:
  `HullSC.exists_two_blocks_of_long_prefix_rotate` and `..._revInv`, which is
  what the mixed cases run on; and that a piece longer than `|p| + 4` carries
  THREE CONSECUTIVE ones, `HullSC.exists_three_blocks_of_long_prefix_rotate`
  and `..._revInv`, which is what the (W4) step of item 6 runs on.  All three
  are proved by writing the offsets down in branches according to where the
  rotation starts, not by counting.
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
* All four cases FROM A PIECE, which is the form the separation applies them
  in: `HullSC.listVal_conj_of_alignedMatch_piece`,
  `HullSC.listVal_conj_of_mirroredAlignedMatch_piece`,
  `HullSC.false_of_mixedMatch_piece` and `..._inv`.  Each runs the window
  count, spends the design's depth clause on the span it finds, and matches
  across; the mixed pair runs the count twice and compares, and the aligned
  pair runs the count, the match and (W4) together inside
  `HullSC.exists_match_with_trivialGap`.
* The four cases at one quadrilateral: `HullSC.listVal_conj_of_sym_pieces`,
  which is the dispatch fed by those four.  What it still takes as hypotheses
  is item 2 as the count, item 3, and the two spellings with their positivity
  -- the same list as the binders above, and nothing else.
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

## The composition, and what is above it

`HullSC.separationNe₂_clause_of_inputs` is the corrected separation at one
core: it chooses `p` by (C1), `B` by (C2) and the run by (C3), spells `y` and
`z` as padded base words with `HullSC.exists_side_spelling₂`, proves the
four-gon's letter clause (a member of the symmetrized closure is admissible
because the relator is, and admissibility survives rotation, formal inverse and
reversal), and hands the quadrilateral to
`HullSC.listVal_conj_of_sym_pieces`.  Its whole hypothesis list is `hδ`,
`hcount` and `hexcl` --- items 1's residue, 2 and 3 --- together with the core,
suitability, and the block-count constant.  (W4) rides in on the core itself,
as the field `disjoint`, and is passed to the four-way through
`E.rel.fam = E.H`.

The exponent list comes from
`HullSC.exists_separated_relator_exponents₂_cross` at radius
`max rho (Cm * 4)`, which is the given `rho` enlarged to what the matching step
asks for; `HullSC.notMem_relBall_of_le` gives the statement's own `rho` back.
That one call discharges `hnodup`, `hsep` and the deep clause together.  The
diagonal-excluding variant `..._diagonal` is no longer called by the chain.

`HullSC.separationNe₂_of_inputs` quantifies that over every `G`, `A`, `N` and
`E`, in the shape `hullRelatorStatement₂_of_separationNe₂` consumes, with the
three clauses quantified the same way and the two constants `cnt` and `δ`
inside the quantifier as existentials --- they belong to the core, and a chain
that fixed them once for all cores would be claiming more than it has.
Composing the two gives `HullSC.hullRelatorStatement₂_of_inputs`, which is the
relator half of Hull's Theorem 5.1 conditional on exactly three clauses:

    hδ     item 1's residue: four-point hyperbolicity of Γ(G, X ⊔ ℋ)
    hcount item 2: the block count, at every member of the closure
    hexcl  item 3: the two same-side exclusions

and on nothing else.  That is the whole standing debt of the chain, and the
first of the three is a hypothesis about the ambient geometry rather than a
gap: items 2 and 3 are the ones that still owe a proof.  Item 6 was the fourth
until (W4) replaced it.

Item 2 is not independent of item 1, though item 1 is marked closed: the count
needs item 1's bound at `mu = 4` for a two-sided figure, and item 1 is
discharged only at `mu = 1` with `n ≤ 6`.  They move together.

## One correction worth keeping

The existential form of the packaged polygon theorem loses exactly what the
aligned branch needs.  From `∃ x x', x · v_q · x' = v_s` the design still forces
`x = 1` and `x' = 1`, so it still forces `e = f`; but `x` is then an anonymous
element of the ball, and the vertex relation the join consumes does not follow.
The named form is not a convenience.
-/
