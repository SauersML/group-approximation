---
rg: 2
id: artin-mod-central-garside-continuous-automatic-proof
kind: route
title: Take the lift with infimum below c, show left multiplication moves the infimum by at most one, and read continuity off the sequential left action on left-greedy forms
target: artin-groups-mod-central-garside-power-are-continuous-automatic
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

Notation as in the target. For `g ∈ A`, `inf(g)` is the largest `k ∈ Z` with
`Δ^{-k} g ∈ A^+`, and `sup(g)` is the least `k` with `g^{-1}Δ^k ∈ A^+`.

**Recalled facts (not re-derived here).**
- (G1) **Garside normal form.** Every `g ∈ A` is uniquely `Δ^{inf(g)} x_1 ⋯ x_k`, with
  `x_i ∈ (1,Δ)` and `x_1 → ⋯ → x_k`. For positive `g` this is the left-greedy form of `g`
  over `(1,Δ]`, whose leading letters are the `inf(g)` copies of `Δ`. (BBCMP §2.3,
  properties (1)–(4) and Charney's characterization.)
- (G2) **Infimum inequalities.** `inf(u) + inf(v) ≤ inf(uv) ≤ sup(u) + inf(v)`.
  (Standard Garside theory: Epstein et al., *Word processing in groups*, Ch. 9;
  Charney 1992.)
- (G3) **Sequential left action.** For `y ∈ (1,Δ]` and a left-greedy word
  `w_1 ⋯ w_n`, the left-greedy form of `y w_1 ⋯ w_n` is `z_1` followed by the
  left-greedy form of `y' w_2 ⋯ w_n`. Here `z_1 = pref(y w_1)` and `y w_1 = z_1 y'` with
  `y' ∈ [1,Δ]`. (BBCMP, proof of Theorem 2.4, case (1).) Iterating, the left-greedy form of
  `y w_1 ⋯ w_n` is the output of a letter-to-letter transducer. Its states lie in
  `[1,Δ]`, it starts in `y`, and it has at most one extra final letter. Output letter `i`
  depends only on `w_1, …, w_i`.
- (G4) **Automatic structures.** BBCMP Theorem 2.4 (via Charney): the Deligne language `L`
  is an automatic structure for `A` in their convention. Then for every fixed `g ∈ A` the
  relation `R^L_g = {(α,β) ∈ L² : π(α) = g π(β)}` is synchronous rational. This follows by
  composing the generator relations, whose length differences are bounded (Epstein et al.,
  §2.3).

**Step 1 (normal forms).** The lifts of `ḡ` are `g z^m`, and `inf(g z^m) = inf(g) + cm`,
because `z = Δ^c` is central. So exactly one lift `g_0` has `inf(g_0) ∈ [0, c)`. It is
positive, and by (G1) its Garside form is a word of `L̄`. Conversely every word of `L̄`
is the Garside form of a positive element with infimum in `[0,c)`. So `L̄ → Ā` is a
bijection. `L̄` is regular: it is the set of words of the finite-state language `L` that
contain no `Δ^{-1}` and at most `c − 1` letters `Δ`. By (G1) those letters are
necessarily leading.

**Step 2 (the infimum moves by at most one).** Let `y ∈ (1,Δ]` and let `b` be the lift in
`L̄`, so `inf(b) ∈ [0,c)`. By (G2), `inf(yb) ∈ [inf(b), inf(b)+1]`, since `inf(y) ≥ 0` and
`sup(y) ≤ 1`. So `inf(yb) ∈ [0, c]`, and the lift in `L̄` of `ȳ b̄` is `yb z^m` with
`m = 0` if `inf(yb) < c`, and `m = −1` if `inf(yb) = c`.

**Step 3 (automatic).** `Ā` is generated as a monoid by the image of `X`, because
`Δ^{-1} = Δ^{c−1} z^{-1}` and every element of `A` is `Δ^{-j}` times a positive element.
By Step 2, for `y ∈ X`,

    R̄_y = { (α,β) ∈ L̄² : π̄(α) = ȳ π̄(β) } = ⋃_{m ∈ {0,−1}} ( R^L_{y z^m} ∩ (L̄ × L̄) ).

Each piece is synchronous rational by (G4), intersected with a product of regular
languages. So `R̄_y` is synchronous rational, and `(X, L̄)` is an automatic structure.

**Step 4 (continuous).** Use BBCMP Proposition 2.1 with `S = X`. Let `y ∈ X` and
`N ≥ 0`, and put `M = N + c + 1`. Let `ḡ, h̄` have `L̄`-words `α, β` with
`|α ∧ β| ≥ M`. These words are the left-greedy forms of the lifts `a, b` (Step 1).
- By (G3), the left-greedy forms of `ya` and `yb` are the transducer outputs on `α` and
  `β`. The two outputs agree on their first `M` letters.
- By Step 2, the `L̄`-word of `ȳḡ` is obtained from the left-greedy form of `ya` by
  deleting `c` leading letters `Δ` when `inf(ya) = c`, and none otherwise. The same holds
  for `yb`.
- `inf(ya) ≤ c < M`, and the leading `Δ` letters of a left-greedy word are exactly its
  infimum. So the first `M` agreeing letters decide whether `inf(ya) = c`, and they
  decide it in the same way for `yb`.
- Hence the `L̄`-words of `ȳḡ` and `ȳh̄` agree on at least `M − c ≥ N` letters.

If `ḡ = h̄`, the transducer output has length at least `|α| ≥ M`, so the `L̄`-word of
`ȳḡ` has length at least `M − c ≥ N`. So Proposition 2.1 applies, and `L̄` is continuous.
□
