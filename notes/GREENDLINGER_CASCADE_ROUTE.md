# The cascade route to Greendlinger's lemma

Three new modules (`Sofic/GreendlingerCascade`, `Sofic/GreendlingerLanding`,
`Sofic/GreendlingerBeyond`) replace the adjacency assumption the old descent
could not do without.  All three are wired into the root; none has been
compiled.

## Why the old route stalled

`Sofic/GreendlingerThreeFactor` runs a descent on minimal conjugate-product
expressions and leaves `LeadingConfinement`: the block the leading factor loses
stops inside the *next* factor's palindrome.  Its own header carries a
configuration satisfying every constraint the six weight moves and `C'(1/6)`
impose while the block runs 21 letters past what the second factor keeps, so the
hypothesis is (very likely) false and the theorems assuming it are a reduction,
not a gate.

The header also records the reason the conclusion survives there anyway: **the
third factor's rotation is untouched, and sits in the word exactly where the
block stops.**  The old descent cannot see this, because it only ever hands the
block to the factor next to it.

## What the cascade is

`exists_residual_step` (unconditional): `W(x :: e) = A ++ W(e).drop N` --- the
reduced word of an expression is the survivor of its leading factor followed by
the reduced word of the rest with a prefix removed.  Iterating and composing the
two drops gives `exists_cascade`: `W(e) = A ++ W(e.drop k).drop N` for *every*
`k`.  So the word of any suffix of the expression is visible in the word of the
whole, shifted by one number.

`GreendlingerAt.transport` carries a located subword back across such a step.
That is the whole mechanism: the descent no longer has to hand the block to its
neighbour, only to whichever factor it stops in.

## The new hypothesis

`CascadeLanding R`: at the head of a minimal expression whose leading
cancellation reaches past its own trailing conjugator, **either** the leading
factor already delivers the located conclusion, **or** the swallow bound holds
and `LandsIn R |M| W(e) |e|` --- the block stops in some later factor, within a
sixth of that factor's rotation past its conjugator.

* `greendlingerAt_of_cascadeLanding` --- the descent, complete, by induction on
  the number of factors, with the jump supplied by the cascade.
* `greendlingerConclusion_of_cascadeLanding` --- the gate.
* `cascadeLanding_of_leadingConfinement` --- **the new hypothesis is a weakening
  of the old one.**  Every case of the old four-case descent produces one of the
  two branches, with the tail itself as the landing site (`A = []`, `N = 0`).
  Since the old hypothesis is refuted by its own header's configuration and the
  new one is satisfied there (the block stops inside `c₃`, so `N ≤ |c₃|` and
  `i = 0` serve), the implication is strict in the direction that matters.

## The trichotomy, and where the residue now sits

`Sofic/GreendlingerBeyond` names the predicate the search is really about ---
`SubwordBeyond R b V`, a Greendlinger subword of `V` beginning at or after `b`
--- and proves the three moves.  At the factor a block of length `b` arrives at,
keeping `P''` and losing `M''` (which eats `k` past its trailing conjugator),
exactly one of three things happens (`blockStop_cases`):

1. `2(k + (b - |c'|)) < |t'|` --- the factor keeps more than half of its rotation
   beyond the block and delivers the subword itself, at position exactly `b`.
   `subwordBeyond_of_keeps`.  **Unconditional.**
2. `|P''| ≤ b` --- the block outruns what the factor keeps; the residual block is
   `b + N₀ - |A₀|` and `subwordBeyond_of_overrun` carries anything found further
   on back across the factor.  **Unconditional.**
3. `|c'| ≤ b < |P''|` and `|t'| ≤ 2(k + (b - |c'|))` --- the block stops strictly
   inside the survivor and the factor has lost at least half of its rotation,
   `b - |c'|` off the front to the block and `k` off the back to its own.

Branch 3 is the entire residue, and it is exactly the classical statement: a
factor in it keeps at most half, and the count says not every factor can be in
it.  Two things are now available that were not:

* `subwordBeyond_of_stops_inside` --- once the block stops, **every factor after
  the one it stops in lies wholly beyond it**, so a subword carried by any of
  them needs no arithmetic at all.  So branch 3 does not have to be settled at
  the stopping factor; it can be settled at any factor after it.
* The recursion terminates: `LandsIn`'s length parameter shrinks by one factor
  per step (`LandsIn.compose`, `landsIn_of_overrun`), so the search is finite.

Reading branch 3 at the factor *after* the stopping one turns the condition into
`N ≤ |c'| + i` with `6i < |t'|` for that factor's own block `N` --- the same
local condition the buried and meet cases of the old descent already discharge.
So what a continuation has to prove is that the factor a block stops in cannot
be followed by a factor whose own block again fails to land, which is the count
in the only form the algebra can state it.

## Status

* Unconditional and new: `drop_add`, `exists_residual_step`, `exists_cascade`,
  `GreendlingerAt.transport`, `LandsIn` + `of_le`/`mono`, `landsIn_of_confined`,
  `LandsIn.compose`, `landsIn_of_overrun`, `exists_tail_step`, `SubwordBeyond` +
  `of_le`, `subwordBeyond_of_keeps`, `SubwordBeyond.compose`,
  `subwordBeyond_of_overrun`, `subwordBeyond_of_stops_inside`,
  `blockStop_cases`, `tailSubwordBeyondBlock_of_subwordBeyond`.
* Conditional on `CascadeLanding`: `greendlingerAt_of_cascadeLanding`,
  `greendlinger_of_cascadeLanding`, `greendlingerConclusion_of_cascadeLanding`.
* Conditional on `LeadingConfinement`: `cascadeLanding_of_leadingConfinement`,
  `greendlingerConclusion_of_leadingConfinement'` (the subsumption).
* Not compiled.  The three modules are imported from `GroupApproximation.lean`.

The second route through `Sofic/GreendlingerDehn` is untouched: its residue is
still the single critical pair with `2|u| = |r| + 1` or `|r| + 2`, and the two
routes still share no machinery, so a proof of either closes the gate.

---

# The longest conjugator (the argument that should close it)

Following the *leading* factor is the wrong move.  Follow the factor whose
**conjugator is longest**.  `Sofic/GreendlingerMaxConjugator` carries the
arithmetic; this section is the argument.

## Setup

Minimal (length, then weight) expression `w = ∏ᵢ Pᵢ`, `Pᵢ = palindrome cᵢ tᵢ`,
`dᵢ = |cᵢ|`, `Tᵢ = |tᵢ|`.  Free reduction of the concatenation `P₁⋯Pₙ` to `w`
matches destroyed letters in a **non-crossing (nested)** pattern, and **no
matched pair lies inside one `Pᵢ`** (each palindrome is reduced, so the
innermost pair of such an arc would be two adjacent cancelling letters of a
reduced word).  Each factor therefore keeps one contiguous chunk
(`GreendlingerChunks.exists_chunk_decomposition`).  Write `λᵢ`, `ρᵢ` for the
destroyed prefix and suffix of `Pᵢ`, and `xᵢ = (λᵢ - dᵢ)⁺`, `yᵢ = (ρᵢ - dᵢ)⁺`
for what that costs the rotation.

## The reading at a junction

Because the matching is nested, the destroyed prefix of `Pᵢ` is matched
**innermost first** against the reversed tail of everything to its left, and
that tail starts with `Pᵢ₋₁`'s own tail: `invRev cᵢ₋₁` (length `dᵢ₋₁`), then
`tᵢ₋₁` read backwards.  Matching letter `k` of the prefix against depth `k` of
that tail forces `cᵢ₋₁ <+: cᵢ` while `k < dᵢ₋₁`.  So:

* positions `[0, dᵢ₋₁)` — conjugator against conjugator, free;
* positions `[dᵢ₋₁, dᵢ)` — `cᵢ` against `tᵢ₋₁`: a **hug**, `2(dᵢ - dᵢ₋₁) ≤ Tᵢ₋₁`
  (`hug_le_of_minimal_reroute`);
* positions `[dᵢ, λᵢ)` — `tᵢ` against `tᵢ₋₁`: a **piece**, `6xᵢ < min(Tᵢ, Tᵢ₋₁)`.

The hug and the piece cannot together cover `tᵢ₋₁` (`no_overrun_of_hug_and_piece`:
a half plus a sixth leaves a third), so the reading never runs off the end of
`tᵢ₋₁`, and the third bullet is unconditional given `dᵢ₋₁ ≤ dᵢ`.

**Crucially the second bullet is empty when `dᵢ₋₁ ≤ dᵢ` has nothing to spend:
the hug eats `tᵢ₋₁`, never `tᵢ`.**  That is the whole point — at a factor whose
conjugator dominates, its own rotation is eaten by pieces only.

## The choice

Let `m` maximise `d` (`exists_max_index`).  Then `d_{m-1} ≤ d_m` and
`d_{m+1} ≤ d_m`, so by the reading above (and its mirror on the right)

  `6·x_m < T_m`  and  `6·y_m < T_m`,

with `x_1 = 0` when `m = 1` and `y_n = 0` when `m = n`.  Hence
`2(x_m + y_m) < T_m` (`keeps_of_two_pieces`) — in fact `3(x_m + y_m) < T_m` —
so `t_m` keeps a contiguous stretch longer than `2T_m/3`, which is an infix of
factor `m`'s chunk and hence of `w`.  **That is Greendlinger's conclusion, with
no hypothesis, no cascade, and no curvature count.**

Two corollaries fall out of the same reading and are worth keeping:

* **Overruns happen only at local minima of `d`.**  If factor `k+1` is consumed
  whole then the block covers all of what it keeps, so the piece at that junction
  is at least `T_{k+1} - y_{k+1} - hug_k`; with `6·piece < T_{k+1}` this forces
  `y_{k+1} + hug_k > 5T_{k+1}/6`, and both hugs are zero unless `d_{k+1}` is
  below both neighbours.  The witness in `GreendlingerThreeFactor`'s header has
  `c₂ = []` — a local minimum — exactly as predicted.
* **The maximising factor is never consumed whole**, since it keeps `2T_m/3`.

## What is not yet nailed down

One step: that the destroyed prefix of `P_m` is matched against `P_{m-1}`'s tail
*for as far as the rotation reaches*.  The nesting gives this innermost-first,
so it holds as long as the destroyed prefix does not outrun factor `m-1`'s own
contribution.  When it does outrun it, the reading continues into factor `m-2`,
where the next segment may be a conjugator (a hug into `t_m`, and `m` and `m-2`
are not adjacent so no reroute bounds it) rather than a rotation.  The bound
available there is `X ≥ d_{m-1} + 5T_{m-1}/12` for factor `m-1`'s contribution
against `hug ≤ T_{m-1}/2 = 6T_{m-1}/12` — the same five-twelfths-against-six
crossing that has blocked every earlier route, now confined to a single junction
adjacent to the maximiser rather than to the whole chain.

This is `MaximalJunction` in `Sofic/GreendlingerMaxConjugator`.  It is strictly
weaker than `CascadeLanding` and much weaker than `LeadingConfinement`: it asks
what one block is matched *against* at one junction, not where any block stops.

The obvious next moves, in order:
1. Formalise the non-crossing matching (it is the nesting of
   `exists_cancellation_decomposition`, iterated) so that "innermost first" is a
   theorem rather than a picture.  Everything above is then bookkeeping.
2. Close the outrun case by choosing `m` to maximise `d` and breaking ties
   toward the *first* such index, so that `d_{m-1} < d_m` strictly; the block
   arriving at `m` is then bounded by a piece at junction `m-1` and the
   five-twelfths bound applies to `m-1`'s contribution, giving
   `2/12 < 5/12` with room.  This is proved for junctions with `d_k < d_{k+1}`;
   what is missing is the same statement one step further left.

## The outrun case, pinned down exactly

Take `m` the **first** index maximising `d`, so `d_{m-1} < d_m`.  Let `X` be
factor `m-1`'s contribution to `U = reduce(P₁⋯P_{m-1})`, i.e. `X = |P_{m-1}| - σ`
where `σ` is what factor `m-1` loses on its left inside `U`.  An outrun means
`λ_m > X`, and then the reading at junction `m-1` forces

  `X ≤ d_m + piece < d_{m-1} + T_{m-1}/2 + T_{m-1}/6 = d_{m-1} + 2T_{m-1}/3`.

* If `d_{m-2} ≤ d_{m-1}`, then `σ` is a conjugator plus a piece, so
  `X > d_{m-1} + 5T_{m-1}/6` — **contradiction, no outrun.**
* If `d_{m-2} > d_{m-1}`, then `σ` is a conjugator plus a hug plus a piece and
  only `X ≥ d_{m-1} + T_{m-1}/3` survives, which does not contradict
  `d_{m-1} + 2T_{m-1}/3`.

So the entire remaining gap is: **factor `m-1` is a local minimum of `d`
(squeezed between `c_{m-2}` and `c_m`, both longer) and is consumed whole**, so
that `t_m` meets `c_{m-2}` — two factors apart, where no reroute identity
reaches.

The tool for exactly that is `norm_le_of_minimal_sendPast`
(`GreendlingerThreeFactor`): the leading factor of any suffix expression may be
conjugated past **any** initial stretch of its tail, at the cost of that
stretch.  Applied to factor `m-2` sent past factors `m-1` and `m`, it is the only
move in the development that bounds a hug between non-adjacent factors, and it is
what the last case wants.  That is the single next step; nothing else in the
argument is open.

## The matching, precisely (and the new tool it needs)

"Innermost first" is not automatic and the earlier phrasing overstated it.  What
is true: all letters of `P_m`'s destroyed prefix pair leftward, so non-crossing
forces their partners to be **strictly decreasing** in the position — partner(0)
leftmost, partner(λ-1) rightmost.  Hence the `t_m` letters (positions `≥ d_m`)
have the partners **closest to the junction**, which is what the argument wants.

The partners need not be contiguous: between consecutive partners there can be a
**gap**, a contiguous self-matched segment.  A gap cannot lie inside one factor
(no arc does).  If a gap consists of whole factors, its concatenation freely
reduces to nothing, so their product is `1` — and `conjEval_block_ne_one`
(new, unconditional, from minimality of the factor count alone) forbids that.
So the only surviving gaps straddle a factor: `[suffix of P_a][P_{a+1}]⋯[P_b]`,
whose product is the inverse of a suffix of `P_a`.

Excluding those is the last thing.  Two handles, both already in the repo:

* `not_absorb_of_minimal` / `not_absorb_inv_of_minimal` — a whole rotation
  cannot sit inside a conjugator.  A gap that swallows `P_{m-1}` whole against
  `invRev c_{m-2}` is exactly that configuration.
* `norm_le_of_minimal_sendPast` — the only move reaching a non-adjacent factor.
  A gap makes `conjEval` of the straddled block equal to the inverse of a suffix
  of `P_a`, which is precisely the quantity that move bounds.

## The outrun case, closed on one branch and budgeted on the other

Take `m` **least** among the maximisers of `d`.  Suppose the destroyed prefix of
`P_m` outruns factor `m-1`'s contribution `B'` to `U = reduce(P₁⋯P_{m-1})`.
Then factor `m-1`'s rotation is eaten exactly, from the left by a hug `g` (from
`c_{m-2}`) and from the right by the hug `h = d_m - d_{m-1}` plus the piece `p`
against `t_m`:

  `g + h + p = T_{m-1}`,  `6p < T_{m-1}`,  `2h + p ≤ T_{m-1}`
  (`overhang_le_of_minimal_reroute_meet`),  `2g ≤ T_{m-1}`.

Where the overrun lands is decided by `|N|`, the block between factors `m-2` and
`m-1`, against `d_{m-2}`:

* **`|N| ≤ d_{m-2}` (lands in a conjugator).**  Then `g` is covered by
  `c_{m-2}`, so `d_{m-1} + g ≤ d_{m-2}`.  The meet bound gives `h ≤ g`;
  maximality gives `d_{m-2} ≤ d_m = d_{m-1} + h`, hence `g ≤ h`.  So `g = h` and
  `d_{m-2} = d_m` — a maximiser earlier than `m`, contradicting the choice of
  `m`.  **This branch is impossible** (`eq_max_of_overrun_into_conjugator`).
* **`|N| > d_{m-2}` (lands in a rotation).**  The block passes `c_{m-2}`
  entirely and meets `t_{m-2}`, so the overrun is a second **piece** of `t_m`.
  The left loss is then two pieces instead of one, and
  `keeps_of_three_pieces` says two sixths on the left and a sixth on the right
  still lose under a half.  **This branch costs nothing.**

So the non-adjacent hug — the configuration that no reroute identity reaches,
and that blocked every earlier route — cannot occur at the first maximiser, and
the only overrun that can occur is one that pays in pieces.

What remains is the recursion: an overrun that passes factor `m-2`'s
contribution as well, and so on down the chain.  Each additional step is again
one of the two branches above, and each overrun consumes a factor whole, so the
chain is finite; what is not yet written down is the bookkeeping that the pieces
accumulated along it stay under a third.  `keeps_of_three_pieces` is the two-step
case; the general one wants `6·Σpieces < 2T`, i.e. at most two overruns, which
is what `not_consecutive_overrun` in `Sofic/GreendlingerChunks` already argues on
the arithmetic side.

## Where it now stands, exactly

Two branches closed outright, at **any** maximiser (no tie-breaking needed):

* **`not_overrun_into_conjugator`.**  If the block from the maximiser eats the
  neighbouring rotation whole, `T ≤ g + h + p`.  Landing among conjugator letters
  would make the far contribution a strict hug inside a conjugator no longer than
  the maximiser's, i.e. `g < h`; with the meet bound `2h + p ≤ T` that gives
  `T ≤ g + h + p < 2h + p ≤ T`.  **So an overrun always lands among relator
  letters, where it is another piece.**  The non-adjacent hug that blocked every
  earlier route cannot occur at a maximiser at all.
* **`not_second_overrun`.**  To pass the factor it landed in, the block must eat
  everything that factor has left; what it eats is a piece, so that factor must
  already be five sixths gone — `5T < 6(p + L)`.  But `L` is a hug and a piece,
  bounded by seven twelfths, and a sixth plus seven twelfths is three quarters,
  not five sixths.  **So a block overruns at most one factor**, and each side
  costs at most two pieces.

Consequently the maximiser loses **at most two pieces on each side**.  If either
side does not overrun, that side costs one piece, the total is three, and
`keeps_of_three_pieces` closes it: `6(p₁ + p₂ + p₃) < 3T` gives
`2(p₁ + p₂ + p₃) < T`, so more than half of `t_m` survives, contiguously, as an
infix of `w`.

**The whole residue is the case where both sides overrun** — four pieces, which
gives a survivor over a third but not over a half.  Four is exactly the classical
threshold: Greendlinger's count produces a boundary region with at most *three*
interior edges, and three is what suffices here too.  So what is left is not a
new obstruction; it is the classical count, in its smallest possible form:

  **at a factor of maximal conjugator length, the factors on both sides cannot
  both be consumed whole.**

Both overruns force their neighbour to be a strict local minimum of `d` with
`d_m - d_{m±1} > 5T_{m±1}/12`, and both force the factor two away to be within a
sixth of maximal (`d_{m∓2} ≥ d_m - p`).  The unspent tools are
`conj_ne_inv_of_minimal` on the non-adjacent pairs and
`norm_le_of_minimal_sendPast`.

### One attack on the last case that does NOT work

Tempting: both overruns make `c_m` hug a rotation on each side, with
`h > T_{m-1}/3` and `h' > T_{m+1}/3`; if the two hugged stretches of `c_m` nested,
the shorter would be a common subword of two symmetrized relators, hence a piece
under a sixth, contradicting the third.  **They do not nest.**  The hug at
junction `m-1` is the *suffix* of `c_m` of length `h` (positions
`[d_{m-1}, d_m)` of `c_m`), while the hug at junction `m` is the *prefix* of
`c_m` of length `h'` (because from `P_m`'s side that junction reads `invRev c_m`,
which reverses the indexing).  They overlap only if `d_{m-1} + d_{m+1} < d_m`,
which nothing forces.  Checked and discarded — do not re-derive.
