---
rg: 2
id: no-four-strand-bigelow-arc-pair-with-at-most-250-crossings-proof
kind: route
title: "Exhaustive crossing-sequence enumeration: no vanishing-pairing arc pair on D_4 with at most 250 crossings"
target: no-four-strand-bigelow-arc-pair-with-at-most-250-crossings
requires: []
artifacts:
  - research/artifacts/burau-four-strand-bigelow-arc-search-2026-09-17.md
  - experiments/burau-arc-orbit-search-2026-09-17/arcfast2.c
  - experiments/burau-arc-orbit-search-2026-09-17/arcpairs_np.c
  - experiments/burau-arc-orbit-search-2026-09-17/run.sh
---

Proof by finite computation. The objects are those in the target claim.

1. **Normal form.** Cut `D_4` along `beta_0` to get a disk `D'`. Its boundary reads `J | L | N | R | J`:
   - `J` is the arc containing both copies of `p_0`;
   - `L` and `R` are the two copies of `beta_0`;
   - `N` is the point `q_3`.

   An arc `alpha` from `q_1` to `q_2` with `m` transverse crossings meets `D'` in three kinds of piece:
   - a stub from `q_1` to the first crossing;
   - `m - 1` pairwise disjoint chords;
   - a stub from the last crossing to `q_2`.

   A homeomorphism of `D'` fixing `∂D'` pointwise does not change the configuration up to homeomorphisms of `D_4` that preserve `beta_0`. Use such homeomorphisms to make three simplifications:
   - slide `q_1` and `q_2` along their stubs to the boundary points of the first and last crossings;
   - move `q_4` inside its region to a boundary gap, or to `J`;
   - by the reflection in the line of `beta_0`, which sends the pairing `p(t)` to `±t^j p(t^{-1})`, make the first crossing arrive on `L`.

   The configuration is now a finite word:
   - for each crossing, the boundary gap where it arrives, with the departure at the mirrored height on the other copy;
   - the positions of the marks.
2. **Minimal position.** Arcs with fixed endpoints are in minimal position iff they have no bigon (Bigelow's Lemma 2.1, arc version; Farb–Margalit §1.2).
   - An innermost bigon has its `alpha`-side equal to a single chord, and its interior contains no puncture.
   - For a same-side chord, the side not containing `J` is a disk bounded by the chord and a segment of `beta_0`. It is a bigon iff it contains no mark.
   - For an L–R chord, gluing `L` to `R` above both endpoints gives a disk bounded by the chord and a segment of `beta_0`. That disk contains `q_3` in its interior, so it is never a bigon.
   - Hence minimal position holds iff every same-side chord encloses a mark.
3. **Pairing.** Bigelow's remark (GT 3, p. 402) gives the exponents:
   - if `alpha'` and `beta'` are arcs of `alpha` and `beta_0` between consecutive crossings and `alpha' ∪ beta'` bounds a `k`-punctured disk, then the exponents differ by `k`;
   - the sign of the difference is `+` when the loop runs counterclockwise.

   By step 2 this disk is the region on the non-`J` side of the chord, and `k` is the number of marks it contains, plus 1 for `N` on an L–R chord. The loop "chord from `cur` to `arr`, then back along the boundary" is counterclockwise exactly when `arr` precedes `cur` in the boundary order, uniformly for both chord types. So `arcfast2.c` computes `p(t)` exactly.
4. **Completeness.**
   - The DFS in `arcfast2.c` tries every gap of the region of `cur`. That is every arrival allowed by disjointness from the earlier chords, plus the finish at the arrival copy of `y`.
   - The top level runs over all 28 choices: the side of `q_4`, the height order of the objects `x_0`, `y` and `q_4`, and the side of `y`.
   - Duplicate listings are harmless for an exclusion result.
5. **Pruning.** Adding a crossing changes one coefficient of `p` by `±1`. So a partial word with `d` crossings and `||p||_1 > M - d` has no completion with at most `M` crossings and `p = 0`. Cutting such branches loses no hit with `m <= M`.
6. **Run.**
   - `arcfast2 4 250 0 5 s s+1` for `s = 0..27` reports `total_hits=0` in every shard.
   - The shard outputs are listed in the artifact. Since `m` is 1-based, the run covers `1 <= m <= 250`.
7. **Controls** (artifact, §Controls).
   - With pruning off, the independent implementation `arcpairs_np.c` (rank array with explicit chord-crossing tests) gives the same leaf counts as `arcfast2.c` for `n = 4`, `m <= 12`, and for `n = 6`, `m = 8`. The `n = 6` count is 759602.
   - For `n = 3`, every leaf with `m <= 40` has `||p||_1 = |p(-1)| = m`. So no pairing cancels, and the model finds 0 hits to `M = 80`. This is consistent with faithfulness for `B_3` and detects wrong exponent or sign rules.
   - For `n = 6`, 60 hits appear at `m = 8`, consistent with unfaithfulness for `n = 6`.

Verification tier: machine computation with the model argument above; a second lane has not re-run it.
