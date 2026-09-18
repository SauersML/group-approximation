# Referee report (gq-referee-b, citation/scope lens): isometric shift frames over UHF bases fail the K-budget

**Reviewed.** `isometric-shift-frames-over-uhf-bases-fail-the-k-budget` and its `-proof` (lane gq-infinite-primes,
9c3ed53c2), read on origin/main (b3ecacc7d).

**Verdict: PASS.** Both imports are used exactly within their hypotheses. No Cuntz–Pimsner theorem is used. The
Cuntz–Pimsner and Leavitt sentences are motivation or directly verified calibration. One title fix, W1.

## Hypothesis match

**`rational-k1-detection-forces-infinite-order-unit-class`, item 1.**

| Requirement | Why it holds |
|---|---|
| `R` a nonzero unital ring | `Q ⊆ B ⊆ R` are unital subrings. |
| A unital map `Q → R` | The same inclusions. |
| `t[1_R] = 0` for some `t ≥ 1` | Item 2 gives `(m−n)[1_R] = 0` with `m ≠ n`. Take `t = |m − n|`. |

**`graded-rings-with-degree-one-units-fail-the-k-budget`.**

| Requirement | Why it holds |
|---|---|
| A unital map `Q → R` | As above. |
| A `Z`-grading | Item 3 assumes one. |
| A unit in `R_1` | `u = Σ_i s_i x_(i1)` with `s_i ∈ R_1` and `x_(i1) ∈ B ⊆ R_0`, so `u ∈ R_1`. It is a unit with inverse `v = (yt)_1`. |

## Steps checked

- **Item 1.** `x = s` and `y = t` satisfy `xy = 1` and `yx = p`, with `sp = s` and `pt = t`. So `1 ~ p`, and
  `[1_R] = [p]_R`, which is the image of `[p]_B`.
- **Matricial `K_0`.**
  - A unital inclusion `M_(n_i)(Q) → M_(n_j)(Q)` multiplies rank by `n_j/n_i`, so it is injective on `K_0`.
  - Hence `K_0(B) ⊆ Q`, with `[1_B] = 1`.
  - *Cancellation.* Idempotents of equal rank over `Q` are equivalent.
- **Item 3.**
  - `x e_11 = x` makes `sx` a row with one entry, `u`. Likewise `yt` is a column with one entry, `v`.
  - `uv = s(xy)t = spt = 1`.
  - `vu` is the `(1,1)` entry of `y p x = e_11`, so `vu = 1`.
  - The intertwining `u^(-1)bu = (y(tbs)x)_(11)` is correct, and it is unused in the graded conclusion, as the route
    says.
- **Item 4.** `p ≠ 0`, because `1 = spt`, so `r > 0`. Items 2 and 3 exhaust `r`.
- **Calibration.**
  - For `L_Q(1,d)`: `Σ s_i t_i = 1` and `t_i s_j = δ_ij` give `p = I_d` and `r = d`, and item 1 gives `(d−1)[1] = 0`.
  - For `U_n ⋊ Z`: `s = u` and `t = u^(-1)` give `r = 1`.
  - Both are verified directly, not cited.

## Cuntz–Pimsner and Leavitt sentences: motivation only

- **Setting.** "This is the shape of a Cuntz–Pimsner ring ... `p` is its Gram matrix" describes the frame's shape. No
  CP result is invoked.
- **Route, item 3.** "the intertwining of the Cuntz–Pimsner shape" is labelled unused.
- **Item 4.** "index-`d` isometries with `(1 − [X]) = (1 − d)` on the rational classes" is covered by item 2 directly.
  The `[X]` phrasing is motivation.
- **"Multi-type bases".** Labelled heuristic, and conditional on (P).

## Scope

- **W1 (title).** "so every such design fails the scalar K-budget" reads as covering all isometric frames over
  matricial bases. The body is narrower:
  - item 4 requires the grading for index `r = 1`;
  - "What is left open" lists ungraded index-one frames and Toeplitz frames.

  Suggested wording: "so every such design of index `≠ 1`, and every graded one of index `1`, fails the scalar
  K-budget".
- **"What is left open".** Accurate.
