---
rg: 2
id: roller-compactifications-of-cube-complexes-are-quantum-rigid
kind: claim
title: For a free cocompact action on a locally finite CAT(0) cube complex, the Roller compactification SFT is quantum rigid at every scale over every field, and so is every closed invariant subset; the proof needs only that walls are uniformly coarsely connected, crossing walls meet, and adjacent parallel walls touch, which fails for walls through unboundedly long relators
distinct_from:
  free-group-boundary-shifts-are-quantum-rigid: that is the tree case (every pair of walls is nested); this adds crossing walls, which commute because they meet in a square, and runs the monotone chains by induction on the number of separating hyperplanes.
  wall-orientation-subshifts-are-quantum-rigid: that is the open question for all wall structures; this proves it for finite-dimensional cube complexes, isolates the three properties the proof uses, and shows the full compactification fails when walls are not uniformly coarsely connected.
  roller-compactifications-of-cube-complexes-are-sfts: that proves the Roller compactification is an SFT; this proves the SFT is quantum rigid, so finite type and rigidity hold together.
---

**ESTABLISHED** (lane proof, elementary; bh-star-b, 2026-09-18; not reviewed; no priority claimed):
parts 1–3. Part 4 is conditional, as stated there.

## Setting

As in `roller-compactifications-of-cube-complexes-are-sfts`:
- `S` acts freely and cocompactly on a locally finite CAT(0) cube complex `X`.
- `Y_2 ≅ \bar X` is the gradient SFT, whose points are the ultrafilters: a chosen halfspace `o(H)` for
  every hyperplane, pairwise intersecting.
- Each site carries the gradients of the finitely many edges at its vertices.

Quantum families are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity` (Q1–Q3). Fix `D`
large enough that every radius-2 ball of `X^1` lies in the `D`-ball of a site.

## Theorem

1. **Rigidity.** `Y_2` is `D`-quantum rigid over every field, for every such `D`. So is every closed
   invariant subset: the Roller boundary, and every minimal subset.
2. **Axioms.** The proof uses only three properties of the wall structure, at scale `D`:
   - (W1) the edges dual to one wall are linked by bounded local consistency rules;
   - (W2) any two crossing walls have dual edges within distance `2D`;
   - (W3) two disjoint walls separated by no third wall have dual edges within distance `2D`.

   Given (W1)–(W3), and local forbidden patterns for non-ultrafilter choices on close pairs, the same
   proof shows that the ultrafilter subshift of any wall structure on a Cayley graph is `D`-rigid.
3. **Finite type and rigidity together.** Every group acting freely and cocompactly on a CAT(0) cube
   complex carries a quantum-rigid SFT, `Y_2`. It is an SFT by the parent node.
   - This covers RAAGs, `Z^n`, `F_n`, and cubulated hyperbolic groups.
   - By part 5 of the parent node, every virtually special group has a finite-index subgroup lying in
     a RAAG with a rigid SFT compactification.
4. **Where it fails.** Suppose some wall's dual edge set is not `2D`-connected, meaning it splits into
   two nonempty parts at distance `> 2D`. Then the full ultrafilter subshift is not `D`-rigid.
   - The reason: two principal points `v`, `u` separated by that single wall differ exactly on its
     dual edges.
   - This was first expected for walls of graphical `C'(1/6)` presentations with relators of
     unbounded length. **Correction (2026-09-19):** every edge also lies on translates of the shortest
     relators carrying its label, so such walls acquire short links, and (W1) there is **undecided**
     (`products-of-trees-refute-cap-coherence-join-caps-restore-it`, Section 4(b)).
   - The original reasoning: a wall meets a relator in two antipodal edges, and relators are
     isometrically embedded (recalled). Whether other paths reconnect the two sides was **not**
     checked.
   - Where (W1) does fail, finite type also fails, because wall consistency across a long relator is not
     a local rule.

## Proof

**Wall projections.** Given a `D`-family, let `P_e = Σ_(a : a(e) = +) E_a(q)` for an edge `e` at the
site `q`. The readings of a shared edge by its two sites agree by (Q3).
- **One projection per hyperplane.** Opposite edges of a square are oriented alike in every point
  (parent node). With (Q2) and (Q3) on the ball containing the square, their projections are equal.
- Edges dual to `H` are connected through squares. So `Q(h)`, the projection onto "the chosen side of
  `H` is `h`", depends only on the halfspace `h`, and `Q(h*) = I - Q(h)`.
- Each `E_a(q)` is the product of the `P_e^(±)` at its site. So it suffices to show that all the `Q(h)`
  commute.

**Crossing pairs.** Two crossing hyperplanes meet in a square, so they have dual edges at one vertex,
and (Q2) makes `Q(h)` and `Q(k)` commute. This is (W2).

**Disjoint pairs: monotone chains.** For halfspaces `h ⊆ k` of disjoint hyperplanes, let `N(h, k)` be
the number of hyperplanes separating `H` from `K`. We show by induction on `N` that
`Q(h) = Q(h) Q(k) = Q(k) Q(h)`.
- **`N = 0`.** The distance between the carriers of `H` and `K` is the number of separating
  hyperplanes. So the carriers share a vertex `x`, and both walls have dual edges at `x`. This is (W3).
  - The choice "`h` and `k*`" is not an ultrafilter pattern, since `h ∩ k* = ∅`, and it is visible in
    `B_1(x)`. Summing the commuting products of (Q3) gives `Q(h) Q(k*) = 0`.
  - So `Q(h) = Q(h) Q(k)`, and (Q2) gives the other order.
- **`N >= 1`.** Take a separating `V` with side `v`, so that `h ⊆ v ⊆ k`.
  - Every hyperplane separating `H` from `V` separates `H` from `K`: it lies on the `H`-side of `V`,
    so the far side of `V`, which contains `K`, lies in one of its halfspaces. The same holds for `V`
    and `K`.
  - So `N(h, v) < N` and `N(v, k) < N`.
  - Then `Q(h) Q(k) = Q(h) Q(v) Q(k) = Q(h) Q(v) = Q(h)`, and symmetrically
    `Q(k) Q(h) = Q(k) Q(v) Q(h) = Q(v) Q(h) = Q(h)`.

Any two disjoint hyperplanes have nested halfspaces. So every pair of wall projections commutes, and
the family commutes. Subsets are rigid by monotonicity of (Q3).

**Part 4.** Principal points are points of `Y_2`. The two principal points on either side of one wall
differ exactly on its dual edges. If those edges split into two parts more than `2D` apart, Lemma 1′
of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere` gives a noncommuting family. ∎

## Calibration

- **Trees.** There are no crossing pairs, and this is the end-shift proof: the chains run along
  geodesics.
- **`Z^2`.** The crossing pairs are the vertical–horizontal pairs, and the parallel chains are the two
  step shifts. This recovers the product computation in `wall-orientation-subshifts-are-quantum-rigid`.
- **Kazhdan groups.** They admit no such structure (part 6 of the parent node), so the theorem says
  nothing about them, as it must.
- **(RA).** Groups acting properly and cocompactly on finite-dimensional cube complexes are exact
  (Campbell–Niblo, recalled). So these rigid SFTs give no counterexample to (RA′). (RA) itself predicts
  that the minimal subsets act amenably. Whether that is in the literature for Roller boundaries was
  not checked.

## Lesson for general BH

**Compression generalizes from trees to cubes exactly.**
- Nested walls form monotone chains, crossing walls commute because they meet.
- So rigidity and finite type hold together on every cubulated group.

**What rigidity needs from a wall structure** is uniform coarse connectivity:
- each wall is locally linked;
- crossing walls meet;
- adjacent parallel walls touch.

**What this means for (RA′).** For the Arzhantseva–Osajda and Osajda constructions, which are
non-exact but Haagerup, it was first claimed that they lose the first property at every scale. That
claim is withdrawn (see the correction in part 4): whether (W1) holds there is undecided.
- What such wall spaces do lose, uniformly, is **finite dimension**: their dual cube complexes are
  infinite-dimensional (recalled). The proof above never uses finite dimension. But the Reiter side
  does: `products-of-trees-refute-cap-coherence-join-caps-restore-it` shows that Reiter functions
  need joins of all independent directions.
- No finitely presented group acting properly and cocompactly on a finite-dimensional cube complex
  contains a non-exact group (Campbell–Niblo, recalled). So at Osajda's input, cube-type dynamics
  must come from infinite-dimensional wall structure.
