---
rg: 2
id: toms-level-two-spanning-reduces-to-relative-hex-proof
kind: route
title: Thickening and filling the level-two set gives a normal form of disjoint non-separating continua; the face form of the spanning principle at level two is then a relative Hex statement, whose two-coordinate version fails on a slit wall
target: toms-level-two-spanning-reduces-to-relative-hex
requires: [toms-two-level-spanning-holds-in-every-dimension, toms-slice-constant-targets-reduce-to-level-spanning]
---

Notation is that of `toms-two-level-spanning-holds-in-every-dimension-proof` (below: the
*parent proof*). `F_nu^0`, `F_nu^1` are the faces, `M(X)` is the set of faces `X` misses, and
`G(X)` is their union. `X` *fails* `nu` if `M(X)` contains a face of coordinate `nu`. A *face
counterexample* is a usc `delta : I^N -> Z_(>=0)` such that every level component `Omega`
fails at least `delta(Omega) + 1` coordinates.

**(Pieces).** Let `delta' >= delta` be usc, and suppose `delta' = delta` off a closed set `U`,
with `delta' = 2 = max delta` on `U`. For `t < 2`, every component of `{delta' = t}` is a
connected subset of `{delta = t}`. So it lies in a component of `{delta = t}`, misses every
face that component misses, and fails at least as many coordinates.

## Part 1: normal form

Let `delta` be a face counterexample with values in `{0, 1, 2}`. Then `H_2 = {delta = 2}` is
non-empty: otherwise `max delta <= 1`, and the level-set form of Theorem 1 in the parent proof
gives a level-1 component face-spanning `N - 1` coordinates or a level-0 component
face-spanning all `N`. Either one fails at most `delta` coordinates.

**Step 1 (thickening).** `H_2` is closed, since `delta` is usc and integer-valued.
- *Clopen cover.* Each component `K` of `H_2` misses faces `F, F', F''` in three different
  coordinates. By the Šura-Bura theorem, some clopen `C_K ⊂ H_2` with `C_K ⊃ K` misses
  `F ∪ F' ∪ F''`, as in Step 1 of the parent proof.
- *Thickening.* Pass to a finite disjoint refinement `D_1, ..., D_r`. Then take closed
  `eps`-neighbourhoods `U_j`, which are pairwise disjoint and each miss three faces in distinct
  coordinates. As shown there, each `U_j` has finitely many components.
- *The new function.* Put `U = ∪ U_j` and `delta' = max(delta, 2 · 1_U)`. This is usc, as the
  maximum of two usc functions.
- *Level 2.* `{delta' = 2} = U`, because `H_2 ⊂ U`. Its components are the finitely many
  components of the `U_j`, each failing at least 3 coordinates.
- *Levels 0 and 1.* These are covered by (Pieces).

So `delta'` is a face counterexample whose level-2 set has finitely many components.

**Step 2 (fills).** Let `K_1, ..., K_r` be the components of `U`. Each misses faces in at
least two coordinates, which is all that Steps 2-3 of the parent proof use.
- *Laminar fills.* The fills `fill(K_j) = I^N \ W_(K_j)` are closed, non-separating, and
  pairwise nested or disjoint. Each misses every face in `M(K_j)`, so it fails at least 3
  coordinates.
- *Each fill is a continuum.* `fill(K)` is `K` together with the components `V ≠ W_K` of
  `I^N \ K`. Each such `cl V` is connected and meets `K`, because `∅ ≠ ∂V ⊂ K`.
- *The maximal fills.* Let `P_1, ..., P_s` be the maximal fills. They are pairwise disjoint
  continua with connected complements. Put `O = ∪ P_i ⊃ U` and
  `delta'' = max(delta', 2 · 1_O)`, which is usc.
- *Level 2.* `{delta'' = 2} = O`. The `P_i` are disjoint, closed, connected, and finite in
  number, so they are exactly the components of `O`. Each fails at least 3 coordinates.
- *Levels 0 and 1.* These are covered by (Pieces).

**Step 3 (the complement).** Steps 4-5 of the parent proof use only that the `P_i` are
disjoint closed non-separating sets, each missing faces in two coordinates. They give that
`R = I^N \ O` is non-empty, connected, and meets all `2N` faces.

This proves Part 1 of the claim. ∎

## Part 2: the reduction

Let `O` and `R` be as in Part 1.

**`R1(3)` implies the face form at `max delta <= 2`.**
- Let `delta` be a face counterexample with `max delta <= 2`. By Part 1 it has
  `max delta = 2`, and we may assume it is in normal form.
- Put `K = {delta = 1} = {delta >= 1} ∩ R`. This is relatively closed in `R`.
- The components of `K` are the level-1 components, so each fails at least 2 coordinates.
- By `R1(3)`, some component of `R \ K = {delta = 0}` meets all `2N` faces. It is a level-0
  component that fails 0 coordinates, which is a contradiction.

**The face form implies `R1(3)`.**
- Given `O` and `K` as in `R1(3)`, write `K = C ∩ R` with `C` closed. Then
  `K ∪ O = C ∪ O` is closed.
- So `delta = 2 · 1_O + 1_K` is usc.
- Its level components are:
  - at level 2, the `P_i`, which fail at least 3 coordinates;
  - at level 1, the components of `K`, which fail at least 2;
  - at level 0, the components of `R \ K`.
- The face form gives some component that fails at most `delta` coordinates. Only a level-0
  component can do so, and it fails 0 coordinates. So it meets all `2N` faces.

**The face form implies (S).** A counterexample to (S) is a face counterexample, since
`F_nu^0 ⊂ A_nu` and `F_nu^1 ⊂ C_nu`. ∎

## Part 3: `R1(2)` is false

Let `N >= 2`, `P = [.4, .6]^2 x I^(N-2)`, `O = P`, and `R = I^N \ P`.

**`P` satisfies the hypotheses with `q = 2`.**
- `P` is a convex continuum. It misses `F_1^0, F_1^1, F_2^0, F_2^1`, so it fails 2 coordinates.
- `R` is covered by the four convex sets `{x_1 < .4}`, `{x_1 > .6}`, `{x_2 < .4}` and
  `{x_2 > .6}`. Each of the first two meets each of the last two, so `R` is connected.

**The set `K`.** Let `K = {x_1 = 1/2} ∩ R`, which is relatively closed in `R`. It is the
disjoint union of the convex sets `{x_1 = 1/2, x_2 < .4}` and `{x_1 = 1/2, x_2 > .6}`, and
these are its components. Each misses both faces of coordinate 1 and one face of coordinate 2,
so each fails 2 coordinates.

**No component of `R \ K` meets all faces.** `R \ K = R ∩ {x_1 ≠ 1/2}` is the disjoint union of
the open sets `R ∩ {x_1 < 1/2}` and `R ∩ {x_1 > 1/2}`. Every component lies in one of them, and
so misses `F_1^1` or `F_1^0`.

As a `delta` (2 on `P`, 1 on `K`, 0 elsewhere), (S) still holds, because `P` fails only
`2 = delta` coordinates. So the hypothesis "three coordinates" in `R1(3)` is exactly the
information that any proof of (S) at level 2 has to use beyond Theorem 1.

The example is flat. The obstruction is not the shape of `K`. It is that level-2 pieces
failing only two coordinates can cut a wall into pieces that each fail two. ∎

## Part 4: flat walls

Suppose `{delta >= 1} ⊂ W = {x_nu = a}` with `0 < a < 1`, and `max delta <= 2`. We show that
some level component fails at most `delta` coordinates.

**Case 1: `delta(p) = 0` for some `p ∈ W`.**
- `{delta = 0}` is open. It contains the two convex slabs `{x_nu < a}` and `{x_nu > a}`, and a
  neighbourhood of `p` that meets both slabs.
- So one level-0 component contains both slabs.
- Every face meets one of the slabs: `F_nu^0` meets the first, `F_nu^1` the second, and every
  other face meets both. So this component fails 0 coordinates.

**Case 2: `delta >= 1` on all of `W`.**
- *Setting up.* Then `{delta = 1} = W \ H` with `H = {delta = 2} ⊂ W` closed. Identify
  `W ≅ I^(N-1)` through the coordinates `mu ≠ nu`.
- *Counting failures.* A set `X ⊂ W` meets `F_mu^e` (for `mu ≠ nu`) if and only if it meets
  the corresponding face of `W`, and it misses both `F_nu^0` and `F_nu^1`. So the number of
  coordinates `X` fails in `I^N` is `1` plus the number it fails in `W`.
- *If some component of `H` fails at most 2 coordinates* in `I^N`, we are done.
- *Otherwise* every component of `H` fails at least 2 coordinates of `W`, so none face-spans
  `N - 2` of the `N - 1` coordinates of `W`.
  - Theorem 1 of the parent proof, in dimension `N - 1`, gives a component `V` of `W \ H` that
    face-spans all coordinates of `W`. For `N - 1 = 1` the hypothesis forces `H = ∅`, and
    `V = W`.
  - `V` is a component of `{delta = 1}`, because `W \ H = {delta = 1}`.
  - It fails exactly one coordinate (`nu`), and `1 <= delta`. ∎

## Part 5: products

Let `delta_1` and `delta_2` be usc and integer-valued on `I^(N_1)` and `I^(N_2)`. Put
`delta(x, y) = delta_1(x) + delta_2(y)`, which is usc on `I^(N_1 + N_2)`.

**The level sets split into clopen products.** Fix `t`. Then
`{delta = t} = ⊔_s L_s`, where `L_s = {delta_1 = s} x {delta_2 = t - s}`.
- Only finitely many `s` occur, because a usc integer function on a compactum is bounded
  above, and here `delta_i >= 0`.
- Each `L_s` is closed in `{delta = t}`. Let `(x_k, y_k) ∈ L_s` converge to `(x, y) ∈ L_(s')`.
  Upper semicontinuity gives `delta_1(x) >= s` and `delta_2(y) >= t - s`. These sum to `t`, so
  both are equalities and `s' = s`.
- So each `L_s` is clopen in `{delta = t}`.

**Components are products of components.**
- A product of connected sets is connected.
- For a component `C` of `A x B`, the projections are connected. So
  `C ⊂ pi_1 C x pi_2 C`, and maximality gives equality.

Hence the level components of `delta` are exactly the products `Omega_1 x Omega_2` of level
components.

**The invariants add.** `Omega_1 x Omega_2` meets a face `F x I^(N_2)` if and only if
`Omega_1` meets `F`, and similarly in the second factor. So:
- the failed coordinates, and the spanned ones, form disjoint unions;
- `c`, `E` and `delta` add (the chamber count is per coordinate).

**Consequences.**
- *Upward propagation.* Take `delta_2 = 0`, whose only level component is `I^(N_2)`; it
  fails nothing. Then the components of `delta` are the sets `Omega_1 x I^(N_2)`, with the same
  `delta` and the same failed coordinates. So a counterexample (to (S), or a face
  counterexample) in dimension `N` gives one in every dimension `N' >= N`, with the same
  maximum.
- *Doubling the failure.* A product of two face counterexamples has every component failing
  at least `(delta_1 + 1) + (delta_2 + 1) = delta + 2` coordinates. ∎

## Part 6: the depth consequence

Suppose (S) holds for all `delta` with `max delta <= 2` in dimension `N >= 5`. By Part 2 this
follows from `R1(3)` in dimension `N`. Take a slice-constant target, and suppose its
`max delta <= 2`.
- (S) gives a level component `Omega` that fails at most `delta(Omega)` coordinates.
- Theorem part 2 of `toms-slice-constant-targets-reduce-to-level-spanning` then gives
  `delta(Omega) >= N/2 > 2`. This is a contradiction.

So the depth is at least `max delta >= 3`. For `N = 5, 6` this equals `ceil(N/2)`, and it is
sharp by the staggered targets (Theorem part 3 there). ∎
