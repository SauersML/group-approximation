---
rg: 2
id: toms-level-two-spanning-reduces-to-relative-hex
kind: claim
title: The spanning principle at max delta = 2 reduces to a relative Hex statement over finitely many disjoint non-separating level-two continua, each missing faces in three coordinates; the version with two coordinates is false, flat level-one walls are impossible, and counterexamples propagate upward in dimension
artifacts:
  - experiments/toms-level-spanning-weighted-2026-09-18/anneal.c
  - experiments/toms-level-spanning-depth-three-2026-09-18/results.json
  - experiments/toms-level-spanning-depth-three-2026-09-18/torus_relative_hex.py
distinct_from:
  toms-two-level-spanning-holds-in-every-dimension: that proves (S) when max delta <= 1 and records two dead inductions; this is the first reduction at max delta = 2, and it shows exactly which extra hypothesis (three missed coordinates on level 2, not two) any proof has to use.
  toms-slice-constant-targets-reduce-to-level-spanning: that reduces depth ceil(N/2) for slice-constant targets to (S); this works on (S) itself at the first open level.
---

**ESTABLISHED** (internal derivation, unreviewed; proof
`toms-level-two-spanning-reduces-to-relative-hex-proof`) for parts 1-5. The principle (S)
at `max delta = 2` stays **OPEN**, and so does the budget case `N = 5`, `beta = 5`.

**Setting.** As in `toms-two-level-spanning-holds-in-every-dimension`. `delta` is upper
semicontinuous (usc) on `I^N` with values in `{0, 1, 2}`. A set *fails* a coordinate `nu`
face-wise if it misses `x_nu = 0` or `x_nu = 1`. A *face counterexample* is a `delta` whose
every level component fails at least `delta + 1` coordinates face-wise. A counterexample to
(S) is a face counterexample, so it suffices to rule these out.

**Theorem.**
1. *Normal form.* If a face counterexample with `max delta = 2` exists, then one exists in
   which `{delta = 2} = O = P_1 ⊔ ... ⊔ P_s`. Here each `P_i` is a continuum, `I^N \ P_i` is
   connected, and each `P_i` misses faces in at least three coordinates. The complement
   `R = I^N \ O` is then connected and meets all `2N` faces.
2. *Reduction.* The face form of (S) at `max delta <= 2` (no face counterexample), in a given
   dimension, is equivalent to the relative Hex statement `R1(3)` there. The face form implies
   (S).

   > `R1(q)`. Let `O` and `R` be as in 1, with "three" replaced by `q`. Let `K ⊂ R` be
   > relatively closed, and suppose every component of `K` fails at least two coordinates
   > face-wise. Then some component of `R \ K` meets all `2N` faces.

3. *`R1(2)` is false* for every `N >= 2`. Take `O = [.4,.6]^2 x I^(N-2)` and
   `K = {x_1 = 1/2} \ O`. So the three missed coordinates of the level-2 pieces are what any
   proof must use. The ambient input of Theorem 1 (unicoherence of the cube) is not enough.
4. *Flat walls.* If `{delta >= 1}` lies in a hyperplane `{x_nu = a}` with `0 < a < 1`, then
   (S) holds. This follows from Theorem 1 of `toms-two-level-spanning-holds-in-every-dimension`,
   applied inside the hyperplane.
5. *Products and monotonicity in `N`.* For usc functions `delta_1` on `I^(N_1)` and
   `delta_2` on `I^(N_2)`, the level components of `delta_1(x) + delta_2(y)` are exactly the
   products of level components. So `delta`, `c`, `E` and the failed coordinates all add.
   Consequences:
   - A counterexample to (S), or a face counterexample, in dimension `N` gives one of the same
     kind in every dimension `N' >= N`, with the same maximum, by taking `delta_2 = 0`.
   - So (S) at a given `max delta` in dimension `N`, or its face form, implies the same
     statement in all lower dimensions.
   - The product of two face counterexamples fails at least `delta + 2` coordinates on every
     component.

**What remains.** `R1(3)`. The configurations that parts 3 and 4 do not already cover are:
- *folded partitions*, where `K ∪ O` is not flat;
- *non-unicoherent `R`*, which happens when some `P_i` has `Ȟ^(N-2) ≠ 0`, for example a solid
  torus when `N = 3`;
- *chaining*, where two `K`-pieces that each fail two coordinates meet the same `P_i`.

A proof of `R1(3)` gives depth at least `3` for slice-constant targets in every `N >= 5`.
So the depth is exactly `ceil(N/2)` for `N = 5, 6` (proof, Part 6).

**Search evidence** (`results.json`). Apart from the annulus control below, no run found a
counterexample; the best score was 1 throughout.
- *(B) at `N = 5`.* The parent node's `anneal.c` was run with `max delta <= 2` and `m = 1`.
  This is the first open budget case: `beta = 5` needs `max delta >= 3`.
- *(S) at `N = 4`.* Same annealer, `max delta = 2`, `m = 1`, three seeds.
- *A level-1 wall with one handle* (`torus_relative_hex.py`). A wall `Y` in `I^3` with a handle
  and level 2 on `H ⊂ Y` is a face counterexample exactly when:
  - every component of `H` meets at most two adjacent sides of `∂Y`, and
  - every component of `Y \ H` misses a side.

  This is the simplest non-unicoherent case of `R1(3)`. The search was on triangulated
  punctured tori, from `8 x 8` to `16 x 16`.

  - *Control.* On an annulus, with the sides on one circle and the other circle free, the
    same search finds counterexamples at once. In the cube, a free circle would let level 0
    leak through the wall. So the closing-off given by the level-0 hypothesis is what a proof
    must use, not the genus.

  The corner points matter. A point between boundary cells of different colours lies in `H`.
  If it is not counted, the search reports spurious counterexamples at once.

This is evidence only.
