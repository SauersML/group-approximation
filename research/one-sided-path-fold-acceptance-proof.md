---
rg: 2
id: one-sided-path-fold-acceptance-proof
kind: route
title: Rows along flow lines are fibre points; flow lines merge toward the end, so an upper determining half-plane identifies all rows at equal height, while a non-determined past grafted onto one branch breaks faithfulness
target: abht-path-folds-accept-exactly-expansive-rational-half-planes
requires:
  - path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
  - triangle-permutive-existence-iff-hex-cone-determinism
---

Notation as in the target. For a flow `y` with end `ξ`, `h = h_y` is ABHT's height, normalized so that
`h(1) = 0`. Along every tree edge, `h` changes by exactly `±1`, increasing along the flow (ABHT, proof of
`configsJuntas`). Each vertex has one out-neighbour (its parent) and `2n − 1` in-neighbours (its children).
For `z = (a, y) ∈ Z_X` and `w ∈ F_n`, the **row at `w`** is `r_w = (a(w t^i))_(i ∈ Z)`.

## Step 0. The rules, restated

`z = (a, y)` lies in `Z_X` iff three conditions hold:
- `y` is a flow point, constant on `t`-cosets;
- every `r_w` has only legal horizontal `X`-dominoes;
- for every flow edge `w → w'`, each pair `(r_w(i), r_(w')(i))` is a legal vertical domino, with `r_w`
  below.

Every tree edge is a flow edge in exactly one direction: if `y(g) ≠ s`, then `y(gs) = s^(−1)`. So these
are all the vertical constraints.

- **(a) `x ⊗ y ∈ Z_X`** for every `x ∈ X`. This is ABHT's first half of `configsJuntas`, and it uses no
  expansivity.
- **(b) Flow lines are points of `X`.** A *flow line* is a bi-infinite path `γ = (w_k)` in which each
  `w_k → w_(k+1)` is a flow edge. Through every vertex there is one: go up along parents and down by
  choosing children. Then `x_γ(i, h(w_0) + k) = r_(w_k)(i)` defines a point of `X`, because `X` is
  nearest-neighbour and all its dominoes are legal by Step 0.

## Step 1. Item 1, "if"

Assume `−e_2` is determining. Let `σ` be a flow line through `1` and put `x = x_σ`.

- **Every row agrees with `x`.** Take `w ∈ F_n` and a flow line `γ` through `w`.
  - The upward rays from `w` and from `1` both end at `ξ`, so they merge at a first common vertex `q`.
  - The rows of `x_γ` and `x_σ` at heights `>= h(q)` come from the same vertices, so the two points agree
    on `Z × [h(q), ∞)`.
  - Because `−e_2` is determining, `x_γ = x_σ`. In particular `r_w = x(·, h(w))`.
- **So `z = x ⊗ y`.** Here `x ⊗ y(w t^i) = (x(i, h(w)), y(w))`, and `h` agrees with ABHT's `j`.

## Step 2. Item 1, "only if" (`n >= 2`)

- **The two fibre points.** Suppose `x ≠ x'` agree on `Z × [c + 1, ∞)`, and let `c` be the largest row on
  which they differ. It exists, because differing rows are bounded above.
- **The graft.** Take any flow `y`, a vertex `q` with `h(q) = c + 1`, and two distinct children `u ≠ u'`
  of `q` (there are `2n − 1 >= 3`). Let `T_u` be the set of vertices whose upward ray passes through `u`.
  Define `z'` from `x ⊗ y` by giving every `v ∈ T_u` the row `x'(·, h(v))` instead.
- **`z' ∈ Z_X`.**
  - Horizontal dominoes are legal in every row.
  - Flow edges inside `T_u` see `x'`, and flow edges outside `T_u` see `x`.
  - The only flow edge leaving `T_u` is `u → q`, and it sees `(x'(·, c), x(·, c + 1)) = (x'(·, c), x'(·, c + 1))`,
    which is legal.
- **`z'` is not of the form `x'' ⊗ y''`.** Its flow is `y`, and the vertices `u, u'` have the same height
  `c` but carry the different rows `x'(·, c)` and `x(·, c)`.

## Step 3. Item 2

- **(⇒)** Restriction `X → A^(Z × N)` is injective and continuous on a compact space, so the letter
  `x(0, −1)` is a continuous function of the restriction. It therefore depends only on
  `x|_([−R, R] × [0, R'−1])` for some `R, R'`.
  - Recode vertically with height-`R'` columns. The new letter at `(i, j − 1)` has:
    - first entry `x(i, j − 1)`, a function of the new letters of row `j` on `[i − R, i + R]`;
    - remaining entries, which are entries of the new letter at `(i, j)`.
  - The recoding is nearest-neighbour: vertical dominoes encode overlap consistency, and horizontal
    dominoes encode legality of each row.
- **(⇐)** Iterating the rule recovers every row below `c` from the rows at `c` and above.

## Step 4. Item 3

- **Freeness and minimality.** ABHT's proofs of `theorem:strongly_aper_FnZ` (TeX ll. 704–717) and of
  minimality (Lemma `minflow` and the theorem after it, ll. 719–786) use `X` only through `z = x ⊗ y`
  and through aperiodicity, respectively minimality, of `X`.
  - For "free iff": a period `(w, i)` of `x ⊗ y` gives a period of `x`, by their argument. Conversely, a
    period `v` of `x` gives the period `t^(v_1)` when `v_2 = 0`. When `v_2 ≠ 0`, it gives a period `(w, v_1)`
    of `x ⊗ y` for a periodic flow `W = w^N` with `|w| = |v_2|` (take `y` with that word).
  - So freeness transfers both ways under faithfulness. The converse direction is a sketch: the sign
    conventions of ABHT's period computation were not re-derived for it.
- **Rigidity, up.** Re-read `path-fold-rigidity-transfer-proof` with the normal form of item 2. It uses:
  - (F1), which is faithfulness;
  - (F2), heights;
  - the rule `φ` giving row `j − 1` from row `j`.

  Steps 2–4 there apply `φ` only from parent to child, i.e. downward. Nothing else about `X` is used.
- **Rigidity, down.** `path-folded-sft-rigidity-pullback-proof` needs only (a) above and the 1-Lipschitz
  surjection `β`, both valid for every nearest-neighbour `X`.
- **Invariance.** Conjugacies and `GL_2(Z)`-conjugacies preserve freeness, minimality and finite
  presentation of the crossed product, hence rigidity between SFTs
  (`sft-crossed-product-fp-iff-quantum-rigid`).

## Step 5. Item 4

- **(⇐)** A rational determining normal `ν` is sent by some `M ∈ GL_2(Z)` to a positive multiple of
  `−e_2`. Then recode to nearest-neighbour form.
- **(⇒)** Being determining is invariant under conjugacy, by Theorem B of
  `triangle-permutive-existence-iff-hex-cone-determinism`, as recalled in
  `sfts-without-two-sided-faults-are-quantum-rigid`. It is also invariant under `GL_2(Z)`. So a faithful
  fold pulls `−e_2` back to a rational determining normal.
- **Ledrappier.** Its rule is the normal form, so `−e_2` is determining.
  - `+e_2` is not: the map `row j ↦ row j − 1` is 2-to-1 and surjective. So there is a nonzero `e` with
    `e|_(rows <= 0) = 0`, built with row 1 all ones and later rows by successive preimages. Then `x` and
    `x + e` agree below row 1.

## Step 6. Item 5

- **The rule in new coordinates.** Let `M(a, b) = (a, a + b)`, of determinant 1. Then
  `x^M(p_1, j − 1) = G(x^M(p_1 + 1, j), x^M(p_1, j))`, since `M e_1 = (1, 1)` and `M e_2 = (0, 1)`.
- **The recoding.** Pass to `2×2` blocks `x^M|_({p_1, p_1+1} × {j, j+1})`, which gives a nearest-neighbour
  SFT. The block at `(p_1, j − 1)` has:
  - bottom entries given by `G` from row `j` at `p_1, …, p_1 + 2`;
  - top entries equal to the bottom entries of the block at `(p_1, j)`.

  That is a one-row rule of radius 2.
- **Other corners.** Rotations by multiples of `π/2` are in `GL_2(Z)`. ∎
