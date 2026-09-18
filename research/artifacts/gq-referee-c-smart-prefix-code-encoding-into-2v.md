# Referee report (gq-referee-c): the prefix-code encoding of SMART into 2V

- **Object:** step 5 of `research/smart-level-zero-return-map-factors-onto-3-adic-odometer-proof.md`, landed
  be2fe0964 by lane `gq-nv-obstruct`. It encodes the 8-state SMART with a size-24 code `P` on (state, head cell)
  and `D = {0, 10, 11}` on cells. The same conjugacy is item 1 of `three-v-contains-aperiodic-rationals-proof`,
  there with separate codes for states and cells.
- **Lens:** independent re-derivation, including reversibility of the transcribed table.
- **Verdict: PASS.**

## 1. The coding is a homeomorphism

- The configuration `(…c_(-1)[q,c_0]c_1…)` maps to the pair
  `(P(q,c_0) D(c_1) D(c_2) ⋯ , D(c_(-1)) D(c_(-2)) ⋯)`.
- `P` is a complete binary prefix code with 24 words. One exists for every size: take a full binary tree with 24
  leaves. `D` is complete as well.
- An infinite binary word factors uniquely as a `P`-word followed by `D`-words, or as `D`-words alone. So the map
  `X = Γ^Z × Q -> C^2` is a bijection, and it sends cylinders to bricks, in both directions. ✓

## 2. F is a bijection (reversibility)

The table is the one in Callard–Salo `distortion-1-smart.tex`, lines 2–35.

**Symbol transitions.** These are `(x_1, a) -> (y_2, b)`:
- `b_1`: `0 -> (d_2, 1)`; `1 -> (q_2, 1)`; `2 -> (q_2, 2)`.
- `d_1`: `0 -> (b_2, 1)`; `1 -> (p_2, 1)`; `2 -> (p_2, 2)`.
- `p_1`: `0 -> (b_2, 2)`; `1 -> (b_2, 0)`; `2 -> (q_2, 0)`.
- `q_1`: `0 -> (d_2, 2)`; `1 -> (d_2, 0)`; `2 -> (p_2, 0)`.

The 12 images are distinct and exhaust `{b_2, d_2, p_2, q_2} × {0, 1, 2}`. ✓

**Move transitions.** `x_2 -> x_1` with a move: `b_2, p_2` move right and `d_2, q_2` move left. They are a
bijection from phase-2 states to phase-1 states.

So every configuration has exactly one successor and exactly one predecessor, and `F` is a homeomorphism.

## 3. F is a prefix replacement on a finite brick partition

- **Phase-1 state, symbol step:** `P(q,a) -> P(q',b)` in coordinate 1, and coordinate 2 is fixed. There are 12
  bricks.
- **Right move** (`b_2`, `p_2`):
  - coordinate 1: `P(q,c_0) D(c_1) -> P(q',c_1)`;
  - coordinate 2: `ε -> D(c_0)`;
  - 18 bricks.
- **Left move** (`d_2`, `q_2`):
  - coordinate 1: `P(q,c_0) -> P(q',c_(-1)) D(c_0)`;
  - coordinate 2: `D(c_(-1)) -> ε`;
  - 18 bricks.

These 48 domain bricks partition `C^2`, since every `P`-word is covered exactly once. `F` is bijective, so the
image bricks partition `C^2` too. Hence `T = code ∘ F ∘ code^(-1) ∈ 2V`. ✓ `Y` is clopen, because its membership
reads the state and one neighbour.

## 4. Calibration

- **Tail re-indexing.** A move re-indexes the whole tail of one coordinate (`D(c_1)w -> w`). That is exactly a
  prefix replacement with `|u| ≠ |v|`. The same mechanism makes a head-adjacent deletion brick-local in
  `gq-referee-c-smart-induced-map-has-brick-local-height-3-renormalization.md` §5.
- **Consistency with the source.** Callard–Salo's §3.1 conveyor-belt model gives the same conjugacy.
