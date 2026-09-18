---
rg: 2
id: smart-induced-map-alternates-head-direction-proof
kind: route
title: Follow each genuine level-0 move to the next genuine one through the table; the direction always flips
target: smart-induced-map-alternates-head-direction
requires:
  - smart-induced-on-genuine-moves-has-exact-tripling
  - renormalization-heights-force-eigenvalue-roots
---

The table is the one in the proof of `smart-induced-on-genuine-moves-has-exact-tripling`. `Y` is:
- `▶_2` or `◀_2` on a nonzero cell;
- `⊳_2` with a nonzero right neighbour;
- `⊲_2` with a nonzero left neighbour.

Cells are numbered from the head at `0`.

**From `▶_2` on `c_0 ≠ 0`.** The head moves right, and `▶_1` reads `c_1`.
- `c_1 = 0`: `0|1` gives `◀_2` on the new `1`. This is in `Y` and moves left.
- `c_1 ≠ 0`: `c_1|c_1` gives `⊲_2` on `c_1`. Its left neighbour is `c_0 ≠ 0`, so it is in `Y` and
  moves left.

**From `⊳_2` with `c_1 ≠ 0`.** The head moves right onto `c_1`, and `⊳_1` reads it.
- `c_1 = 1`: `1|0` gives `▶_2` on the new `0`, which is not in `Y`. It moves right, and `▶_1` reads
  `c_2`.
  - If `c_2 = 0`: `0|1` gives `◀_2` on a `1`, which is in `Y`.
  - If `c_2 ≠ 0`: it gives `⊲_2` on `c_2` with left neighbour `0`, which is not in `Y`. That moves
    left, `⊲_1` reads the `0`, and `0|2` gives `◀_2` on a `2`, which is in `Y`.

  Either way the result moves left.
- `c_1 = 2`: `2|0` gives `⊲_2` on the new `0`, with left neighbour `c_0`.
  - If `c_0 ≠ 0`, this is in `Y` and moves left.
  - If `c_0 = 0`, it moves left, `⊲_1` reads `0`, and `0|2` gives `◀_2` on a `2`, which is in `Y`
    and moves left.

**Mirror cases.** `◀_2` and `⊲_2` are the mirror images, with every first return moving right.

So the first return of any right-moving `y ∈ Y` is left-moving, and conversely: `δ(S y) = δ(y) + 1`.
The eigenfunction `(-1)^δ` is continuous, since `δ` reads only the state. ∎ (item 1)

**Item 2.** Item 1 makes `Y = B ⊔ S B` with `S^2 B = B`, so `S` is the height-2 tower over `S^2|_B`.
By item 1 of `renormalization-heights-force-eigenvalue-roots`, a height-2 renormalization forces
`E(S) = {μ : μ^2 ∈ E(S)}`. Since `-1 ∈ E(S)`, this gives `i ∈ E(S)`. Take `f` with
`f ∘ S = i f`. Then `f^2` is an eigenfunction for `-1`. `S` is minimal, being induced from the
minimal SMART map, so `f^2 = c (-1)^δ` for a constant `c`. After rescaling, `f` takes values in
the fourth roots of unity, and `C = {f = 1} ⊆ B` satisfies `S^2 C = {f = -1} = B ∖ C`. ∎
