---
rg: 2
id: no-two-sided-fault-sfts-have-rich-strips-in-all-directions
kind: claim
title: A free Z^2 SFT without two-sided faults is, in every rational direction, the spacetime of a surjective strip automaton on an aperiodic non-sofic strip subshift of at least quadratic complexity; products of Z-subshifts always have two-sided faults
distinct_from:
  triangle-permutive-sfts-have-one-sided-total-faults: that gives these constraints for rows, columns and antidiagonals of quasigroup spacetimes; this gives them for every rational direction of every SFT in the wider class of free-minimal-sft-without-two-sided-faults-exists, and adds the product obstruction.
  permutive-triangle-sfts-are-quantum-rigid: that proves that a periodic row of a triangle-permutive SFT gives a periodic point; the strip version here holds in every rational direction with a determining side.
---

**ESTABLISHED (2026-09-18)** through the proof below. Lane proof (bh-free-35), elementary, not independently reviewed.
No priority is claimed; items 1–3 extend the row statements of the two required nodes to all rational directions.

## Setting

`Ω ⊆ A^(Z^2)` is a free SFT with no two-sided fault (determining normals as in
`sfts-without-two-sided-faults-are-quantum-rigid`). Fix a primitive `v ∈ Z^2`. Choose `M ∈ GL_2(Z)` with `M e_1 = v`
and recode `x ↦ x∘M`. This is a conjugacy of `Z^2`-subshifts up to the automorphism `M`, and it preserves freeness,
SFT-ness and the determining property. So the line `Rv` becomes horizontal, and, after possibly also reflecting
`e_2 ↦ −e_2`, its determining normal is `e_2`.

## Theorem

1. **Strip automaton.** There are `w, r >= 1` and a continuous map `Φ : S → S` with the following properties.
   - `S` is the subshift (for the `e_1`-shift) of height-`w` horizontal strips of `Ω`.
   - `Φ` commutes with the `e_1`-shift, is given by a block map of radius `r`, and is surjective.
   - `Ω` is the set of configurations whose consecutive strips follow `Φ`: row `j + w` is a local function of rows
     `j, …, j + w − 1`.
   - `w` may be taken as large as desired. Once `w` is at least the expansivity width (if there is one), `Φ` is
     injective iff the line `Rv` is expansive. So at each non-expansive rational line the automaton is non-injective
     for every `w`, and the opposite normal is not determining.
2. **No periodic strip.** `S` has no `e_1`-periodic point. In particular `S` is not sofic, and neither is the
   projective subdynamics of `Ω` along `v` in any width.
3. **Quadratic strip complexity.** Let `p_S(m)` be the number of `w × m` blocks of `S`. Then
   `p_S((1+2r)n) > n²/2` for every `n >= 1`.
4. **Products are excluded.** Let `X_1, X_2` be `Z`-subshifts with `X_1` infinite, and put
   `Ω' = {x(i,j) = (x_1(i), x_2(j))}`. Then the vertical line is a two-sided fault of `Ω'`.
   - The same holds for any SFT that is conjugate to such a product.
   - So no product substitution tiling (for instance, a product of two primitive aperiodic substitutions), and nothing
     conjugate to one, satisfies `free-minimal-sft-without-two-sided-faults-exists`.
5. **Corner determinism is not enough.** For a 4-way deterministic Wang tile set (Kari–Papasoglu type), the corner rules
   alone make every normal off the axes determining; the axes need more.
   - Across a vertical line, a column is determined by its left (or right) colours only up to one seed tile.
   - Two points that agree on a half-plane and differ on the next column differ on that whole column (a total fault).
   - An axis line has a determining side iff the global rules force the seed on one side.

## Proof

**Item 1.** In the recoded coordinates `e_2` is determining. By Step 1 of `sfts-without-two-sided-faults-rigidity-proof`
there is a rule `F` with `f_2 < 0` for all `f ∈ F`. Put `w = −min f_2` and `r = max |f_1|`.
- Then `x(z)` is a function of `x` on `z + F`, which lies in rows `z_2 − w, …, z_2 − 1` and columns within `r` of `z_1`.
- This defines `Φ`, which is shift-commuting and of radius `r`. Surjectivity holds because every strip of a point has
  a predecessor strip in the same point.
- **Injectivity.** Enlarging `w` keeps `F` a rule. If `Φ` is injective it is a homeomorphism of the compact space `S`.
  Then a strip determines the rows below it as well as above, so the line is expansive. Conversely, if the line is
  expansive with width `R <= w`, a height-`w` strip determines the whole point, in particular the row below it, so
  `Φ` is injective.
- **Opposite normal.** If `−e_2` were determining too, the strip would determine both sides and the line would be
  expansive.

**Item 2.** Let `s ∈ S` have period `p e_1`.
- All `Φ^k(s)` have period `p e_1`, and there are finitely many such strips. So `Φ^a(s) = Φ^(a+b)(s)` for some `a`
  and `b >= 1`.
- The upper half-configuration generated from `Φ^a(s)` then has periods `p e_1` and `b e_2`.
- Every finite pattern of it occurs in `Ω`, since it is part of a point of `Ω`. Extend it periodically to all of
  `Z^2`. Every window of the extension is a window of the half-configuration, so it is legal, and as `Ω` is an SFT
  the extension lies in `Ω`.
- This periodic point contradicts freeness. A nonempty sofic `Z`-subshift has a periodic point, so `S` is not sofic.

**Item 3.**
- **Block bound.** Rows `j >= 0` on the columns `[0, n)` are determined by the strip rows `[−w, 0)` on the columns
  `[−rk, n + rk)`, for the first `k` rows. So the number of `n × k` blocks satisfies `P(n,k) <= p_S(n + 2rk)`.
- **Cyr–Kra.** Every point of `Ω` is aperiodic. By Cyr–Kra (arXiv:1208.4090, Theorem `mainthm`, as read at source in
  `triangle-permutive-sfts-have-one-sided-total-faults`), an aperiodic configuration has `P_x(n,k) > nk/2` for all
  `n, k`. This is applied in the recoded coordinates; `x∘M` is again an aperiodic `Z^2`-configuration.
- **Conclusion.** Take `k = n`: `p_S((1+2r)n) >= P_x(n,n) > n²/2`.

**Item 4.** First, the one-dimensional lemma: if `X_1` is infinite, some `x ≠ y ∈ X_1` agree on `[0, ∞)`. The
mirror statement, with a pair agreeing on `(−∞, 0]`, follows by reflection.
- Suppose no such pair exists. By compactness `x_(−1) = f(x_[0,m])` for some `m` and some function `f`.
- Then for `n > m` every word of length `n+1` is determined by its last `n` letters. So the number of words
  `L_(n+1) <= L_n`, and the complexity is bounded, say by `K`.
- `K + 1` distinct points would give `K + 1` distinct central words once `n` is large. So `X_1` has at most `K` points,
  a contradiction.

Now take `x ≠ y` agreeing on `[0, ∞)`, and any `x_2 ∈ X_2`. The points `(x, x_2)` and `(y, x_2)` of `Ω'` agree on the
right half-plane and differ on the left, so the normal `−e_1` is not determining. The mirror pair shows that `e_1` is
not determining either. Determining normals are conjugacy invariant (Theorem B of
`triangle-permutive-existence-iff-hex-cone-determinism`).

**Item 5.**
- **Normals.** The SW rule `{−e_1, −e_2}` makes every normal in the open first quadrant determining. The other three
  corner rules do the same for the other open quadrants.
- **Seeds.** Given the left colours of a column, SW determinism fixes each tile from the one below and NW determinism
  from the one above. So one tile fixes the whole column, and two columns with the same left colours agree
  everywhere or nowhere.
- **Seeds on the right.** The same holds from the right using NE and SE.
- So an axis line has a determining side exactly when the rules of `Ω` force the seed on that side. ∎

## Lesson for general BH

A determinism-rigid free SFT carries a surjective strip automaton across every rational line.
- In every rational direction, rows are moved by a surjective strip automaton.
- At every non-expansive rational direction that automaton is non-injective (an irreversible time arrow). It acts on a
  non-sofic row language of at least quadratic complexity. At expansive directions the automaton is injective, and
  no irreversibility is needed.
- Products of one-dimensional systems (in particular product substitution tilings) never qualify, because a
  one-dimensional infinite subshift always has asymptotic pairs on both sides.
- Corner-deterministic tile sets fail exactly at the axes unless seeds are forced.

**Correction (bh-free-35, 09-18, after refereeing `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`).**
- The first version of this paragraph said the time arrow must be irreversible across *every* rational line, and
  that self-simulation must run inside a Ledrappier-type irreversible rule. Neither follows from the theorem.
- The theorem forces irreversibility only at non-expansive lines. A side-local hierarchical design can make every
  rational line expansive, since strips read all levels through crossing wires.
- The crossing-wire fixed points of bh-g2-fixedpoint-a are rigid by co-location and decimation, with no
  Ledrappier-type rule. They are consistent with every item above.
