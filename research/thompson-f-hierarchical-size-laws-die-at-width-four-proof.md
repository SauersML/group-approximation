---
rg: 2
id: thompson-f-hierarchical-size-laws-die-at-width-four-proof
kind: route
title: Complete tops are forced, levels are read off sizes, a limit model has equal middle laws, and domination plus a ratio pair give a contradiction at every width at least 4
target: thompson-f-hierarchical-size-laws-die-at-width-four
requires: []
artifacts:
  - experiments/thompson-f-size-levels-2026-09-17/hierarchical_kill.py
  - experiments/thompson-f-size-levels-2026-09-17/hierarchical_kill.out
---

Notation, the class `H`, `T`, `X_v`, `Ψ_mid` and the verbatim citations (the defect `D_λ`, Lemma 1 on
Guba words) are those of the target. Suppose, for contradiction, that `η_n ∈ H` and `D_n → 0`.

**Step 0 (the tops).** By Lemma 1, `z ∈ sM` iff the first `m + 1` trees of `z` contain `σ_s`, and then
`split_s z` is the unique `y` with `z = s y`. A node of depth `h < d` of root `r` lies in the rooted
subforest consisting of the path from `r` to it (`h + 1 <= d` carets) completed by `d − h − 1` carets anywhere
below it, and that subforest is some `σ_s`. So `∩_s {z ∈ sM}` is exactly the event that the complete depth-`d`
tops are present, i.e. `T`. The pieces of `σ_s` are nodes of the tops, they partition the depth-`d` leaves,
and they are listed left to right, so `p_0` contains the leftmost and `p_w` the rightmost depth-`d` leaf.
Hence every middle piece `x` is a union of middle leaves and, on `T`,

`|p_j(s)| = (2^(d − h(x)) − 1) + Σ_(v ≤ x) |X_v|`,   where `x = x_j(s)` has depth `h(x) <= d`.   (1)

**Step 1 (reduction to equal laws).** Fix `s`. `Ψ_* μ_n` has mass `1` and `Ψ_* ρ_s` has mass `η_n(sM)`, where
`ρ_s` is the law of `split_s Z_n` on `{Z_n ∈ sM}`. Write `D_s` for the `s`-term of `D_n`. Then
`D_s >= 1 − η_n(sM)`, and `||(b − a)_+|| = η_n(sM) − 1 + D_s <= D_s` for `a = Ψ_* μ_n`, `b = Ψ_* ρ_s`, so
`||a − b|| <= 2 D_s`. By Step 0, `P(T^c) <= Σ_s (1 − η_n(sM)) <= D_n`, and restricting `ρ_s` to `T` moves it by
at most `D_n`. So `ν_s = law(Ψ_mid(split_s Z_n); T)` satisfies `||ν_s − Ψ_* μ_n|| <= 3 D_n`, hence
`||ν_s − ν_(s')|| <= 6 D_n → 0`. The same bound holds for every measurable function of `Ψ_mid(split_s Z_n)`
(pushforward is a contraction), and for any refinement of `Ψ_mid` it is implied by the refinement's
bound (coordinate projection is a contraction). This proves the refinement clause, and from now on we
condition on `T` (probability `→ 1`).

**Step 2 (levels are read off sizes).** For a node `x` of the tops made of middle leaves put
`ℓ(x) = max_(v ≤ x) ℓ_n(v)` and, if `ℓ(x) >= 1`, `c(x) = Σ_(v ≤ x, ℓ_n(v) = ℓ(x)) c_n(v)`. By (H4), for `ℓ' < ℓ`,
`Λ_ℓ' / Λ_ℓ <= (Λ_ℓ' / θ_(ℓ'+1)) (θ_ℓ / Λ_ℓ) → 0` in probability, since `θ_(ℓ'+1) <= θ_ℓ`. With (1), (H2), (H3)
and `2^d` bounded:
- on `{ℓ(x) = 0}`, `|x|` is tight;
- on `{ℓ(x) = ℓ >= 1}`, `|x| / Λ_ℓ − c(x) → 0` in probability, and `c(x)`, `1 / c(x)` are tight by (H1).

Define the classifier `κ_n(N) = #{ℓ : N >= θ_(ℓ,n)}` on sizes `N`. By (H4) and `θ_1 → ∞`,
`P(κ_n(|x|) ≠ ℓ(x)) → 0` for every such `x`. Likewise, on `{ℓ(x) = ℓ(y) = ℓ >= 1}`,
`|x| / (|x| + |y|) − c(x) / (c(x) + c(y)) → 0` in probability (the random scale `Λ_ℓ` cancels).

**Step 3 (a limit model with exactly equal laws).** Let `V_n = (ℓ_n(v), c_n(v), Y_n(v))_v` over middle leaves,
with `Y_n(v) = |X_v| 1{ℓ_n(v) = 0}`. By (H1), (H2) and finiteness of the levels, `V_n` is tight in
`({0..L} × (0,∞) × N)^(middle leaves)`, so along a subsequence `V_n ⇒ V = (ℓ(v), c(v), Y(v))_v` with
`c(v) ∈ (0, ∞)`. Extend `ℓ(x)`, `c(x)` to `V` by the same formulas and put, on `{ℓ(x) = 0}`,
`N(x) = 2^(d−h(x)) − 1 + Σ_(v ≤ x) Y(v)`. For a word `s` let
`F_s(V) = ( (ℓ(x_j(s)))_j , (r_(ij)(s))_(i≠j) , (N(x_j(s)) 1{ℓ(x_j(s)) = 0})_j )`, with
`r_(ij)(s) = c(x_i)/(c(x_i) + c(x_j))` when `ℓ(x_i) = ℓ(x_j) >= 1` and `r_(ij)(s) = −1` otherwise. `F_s` is continuous
on the state space (levels are discrete, `c > 0`). Let `G_(s,n)` be the same vector computed from the observation
`Ψ_mid(split_s Z_n)`: `κ_n` of the sizes, the size ratios, and the sizes themselves when classified `0`.
By Step 2, `G_(s,n) − F_s(V_n) → 0` in probability. By Step 1 the laws of `G_(s,n)` and `G_(s',n)` are
`o(1)`-close in total variation. So for bounded Lipschitz `f`, `E f(F_s(V_n)) − E f(F_(s')(V_n)) → 0`, and in the
limit

`law F_s(V) = law F_(s')(V)`   for all words `s, s'`.   (2)

All pointwise relations (`ℓ(x) = max` over leaves, `c(x) = Σ` at the top level, (1) for `N`) hold for `V`.

**Step 4 (collapse to one level; the four width-4 bases).** Work in the limit model. Let the base be one of
`(m, d) = (0,4), (1,3), (2,2), (3,1)`.
- (a) *Domination.* If position `j` holds `x = x_j(s) ⊋ y = x_j(s')`, then `ℓ(x) >= ℓ(y)` pointwise and, by (2),
  `ℓ(x) =_d ℓ(y)`. Since levels are finite-valued, `ℓ(x) = ℓ(y)` almost surely.
- (b) *Propagation.* If for one word `s` and one pair of positions `(i, j)` the identity `ℓ(x_i(s)) = ℓ(x_j(s))`
  holds a.s., then, since it is an event of the level block of `F_s(V)`, (2) gives it for every word.
- (c) *Thresholding.* For `t ∈ {1..L}` put `b_t(v) = 1{ℓ(v) >= t}`. Then `max_(v ≤ x) b_t(v) = 1{ℓ(x) >= t}`, so
  every a.s. identity `ℓ(x) = ℓ(y)` holds a.s. for every `b_t`. Hence if **every** Boolean `b` on the middle
  leaves that satisfies the identities collected so far has `max_(x_i(s)) b = max_(x_j(s)) b`, then
  `ℓ(x_i(s)) = ℓ(x_j(s))` a.s. (two different finite levels are separated by some threshold `t`).
- `hierarchical_kill.py` enumerates all Boolean `b` (`2^14`, `2^14`, `2^10`, `2^6` of them), imposes (a), iterates
  (b) with the test (c) to a fixpoint, and finds that only `b ≡ 0` and `b ≡ 1` survive (`hierarchical_kill.out`,
  "step c"). By (c), for every `t` all `b_t(v)` coincide a.s. So **all middle leaves carry one common level
  `ℓ*`** a.s., and every middle piece of every word has level `ℓ*`.

By hand for `(0,4)`: domination gives `ℓ(0010) = ℓ(0011)`, `ℓ(0100) = ℓ(0101)`, `ℓ(0110) = ℓ(0111)`,
`ℓ(010) = ℓ(011)` and their mirrors. So the word `{ε, 0, 01, 010}` (middle `0100, 0101, 011`) has a constant
level vector, and by (2) every word's vector is constant; with the domination identities this forces the
14 middle leaves to one level. For `(3,1)`, in `root:address` form the middles are `(0:1, 1, 2)`,
`(1:0, 1:1, 2)`, `(1, 2:0, 2:1)`, `(1, 2, 3:0)`. Domination gives `ℓ(1:0) = ℓ(1:1) = b` and `ℓ(2:0) = ℓ(2:1) = c`.
The second word's vector is `(b, b, c)`, so by (b) the first two coordinates of `(b, c, c)` agree and `b = c`;
then every vector is constant.

**Step 5 (contradiction).**
- *If `P(ℓ* >= 1) > 0`.* Take the ratio pair of the base (target, table): words `s, s'` with the same node `x`
  at position `i` and `y = x_j(s) ⊋ y' = x_j(s')`. On `{ℓ* >= 1}` both `r_(ij)` are defined and
  `c(y) − c(y') >= c(v) > 0` for a middle leaf `v ≤ y` not below `y'`, which has level `ℓ*`. So
  `r_(ij)(s) < r_(ij)(s')` there. But `{ℓ* >= 1} = {r_(ij)(s) >= 0} = {r_(ij)(s') >= 0}`, and (2) gives
  `E[r_(ij)(s) 1{r_(ij)(s) >= 0}] = E[r_(ij)(s') 1{r_(ij)(s') >= 0}]`. Contradiction.
- *If `P(ℓ* = 0) > 0`.* Take a domination pair `x ⊋ y` at position `j` (it exists, table). By (1),
  `N(x) >= N(y) + 1` on `{ℓ* = 0}`, since `x` has more top carets below it and at least as many leaves. By (2)
  (third block of `F`), `E[arctan N(x) 1{ℓ* = 0}] = E[arctan N(y) 1{ℓ* = 0}]`. Contradiction.

As `P(ℓ* >= 1) + P(ℓ* = 0) = 1`, `D_n → 0` is impossible for the four bases.

**Step 6 (every width `>= 4` by embedding).** Steps 1–3 hold for every `(m, d)`. Steps 4–5 use only the words
of one sub-family `S'` and positions `1, 2, 3`, so it suffices to find `S'` and a base `B` with:
the positions `1, 2, 3` of the words of `S'` hold the middle pieces of the words of `B` at positions `1, 2, 3`,
where each depth-`d_B` leaf `u` of `B` is replaced by a fixed node `ι(u)` of the tops (a **block**: the
middle depth-`d` leaves below `ι(u)`). Then (2) restricted to `S'` and those positions is the base's (2)
for the block levels `ℓ(ι(u)) = max` over the block, and blocks satisfy everything Steps 4–5 use:
- (a)–(c) are identities between maxima over unions of blocks, so the Boolean check applies verbatim with
  blocks as atoms;
- Step 5 needs `c(ι(u)) > 0` on `{ℓ* >= 1}` (true: some leaf of the block has level `ℓ*`) and strict growth of
  `N` along strict inclusions (true by (1)).

The embeddings (the fixed parts are chosen once; the remaining carets are placed on a fixed root so that the
positions `0..4` of the base are unchanged):
- `d >= 4, m >= 1`: root `0` carries a `4`-caret rooted tree from the `(0,4)` family, root `m` a fixed rooted
  subforest with `d − 4` carets (roots `1..m−1` bare). Blocks: depth-`4` nodes of root `0`.
- `d >= 5, m = 0`: `σ = {ε} ∪ 0σ' ∪ 1τ` with `σ'` from the `(0,4)` family at node `0` and `τ` a fixed rooted
  tree of `d − 5` carets at node `1` (empty if `d = 5`). Blocks: depth-`5` nodes below `0`.
- `d = 3, m >= 2`: roots `0, 1` carry a word of `(1,3)`, roots `2..m` are bare. Blocks: depth-`3` leaves.
- `d = 2, m >= 3`: roots `0, 1, 2` carry a word of `(2,2)`, the rest bare.
- `d = 1, m >= 4`: roots `0..3` carry a word of `(3,1)`, the rest bare.

In each case the pieces of the base occupy positions `0..4` in order, since pieces are listed left to right
and every other caret lies to the right. Every middle block of the base is a middle block of the big set
(it avoids the extreme leaves, which sit in positions `0` and `w`). Together with the bases `(0,4)`, `(1,3)`,
`(2,2)`, `(3,1)` this covers all `d >= 1` with `m + d >= 4`. As an independent check, `hierarchical_kill.py` also
runs the widths-5 sets `(4,1)`, `(3,2)`, `(2,3)` directly, with the same verdict. ∎

**Step 7 (why width 3 survives).** For `(0,3)`, `(1,2)`, `(2,1)` the script finds the same collapse to a single
level but **no ratio pair**: there are only two middle positions and no two words share a middle node while
nesting at the other one. That is exactly the room used by Theorem 1 of
`thompson-f-tree-size-observations-have-zero-defect`, whose law lies in `H` (target, Sharpness).
