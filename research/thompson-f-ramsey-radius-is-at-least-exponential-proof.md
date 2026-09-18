---
rg: 2
id: thompson-f-ramsey-radius-is-at-least-exponential-proof
kind: route
title: Color B_n by whether y⁻¹ breaks at 1/2, use four words that move 1/2 to p with jumps 0 to 3 to force a breakpoint at each p of the Schreier ball with probability 1/4, count breakpoints per letter, and grow the Schreier ball by ping-pong on [1/2, 3/4)
target: thompson-f-ramsey-radius-is-at-least-exponential
requires: [moore-ramsey-criterion-for-amenability]
artifacts:
  - experiments/ramsey-lamp-forcing-2026-09-17/lamp_forcing.py
  - experiments/ramsey-lamp-forcing-2026-09-17/lamp_forcing.json
---

Notation is as in the claim. From `moore-ramsey-criterion-for-amenability` this uses only the verbatim definition of
"ε-Ramsey", the definitions of `R_{G,S}` and `μν`, and the two monotonicity facts: `R` is nondecreasing and `R(m) ≥ m`.

**Step 0 (reading the definition with point masses).** Suppose `B_n` is 1/2-Ramsey w.r.t. `B_m`, and `E ⊆ B_n`. Then
there is `ν ∈ P(B_n)` with `P(B_m)ν ⊆ P(B_n)`. Taking `μ = δ_e` gives `supp ν ⊆ B_n`, and taking `μ = δ_g` gives
`g·supp ν ⊆ B_n` for all `g ∈ B_m`. Moreover `|δ_gν(E) − δ_{g′}ν(E)| ≤ 1/2` for all `g, g′ ∈ B_m`, where

`δ_gν(E) = Σ_{gy ∈ E} ν(y) = P_ν(gy ∈ E)`.

(`ν` is a finitely additive measure on a finite set, hence an ordinary probability vector.)

**Step 1 (PL facts about the generators).** Take `x_0` and `x_1` as the standard maps: `x_0` has breakpoints
`(1/2, 1/4)` and `(3/4, 1/2)`, and `x_1` has breakpoints `(1/2, 1/2)`, `(3/4, 5/8)` and `(7/8, 3/4)`. The script
`lamp_forcing.py` confirms their binary actions exactly. For each letter `s ∈ S ∪ S⁻¹`:
- (i) `s` has at most 3 breakpoints in `(0,1)`, and at each one `β_s(t) := log₂s′(t+) − log₂s′(t−) ∈ {−1, +1}`.
  - `x_0`: breakpoints `1/2, 3/4`, jumps `+1, +1`.
  - `x_0⁻¹`: breakpoints `1/4, 1/2`, jumps `−1, −1`.
  - `x_1`: breakpoints `1/2, 3/4, 7/8`, jumps `−1, +1, +1`.
  - `x_1⁻¹`: breakpoints `1/2, 5/8, 3/4`, jumps `+1, −1, −1`.
- (ii) `x_1(1/2) = 1/2` and `β_{x_1}(1/2) = −1`. The slope of `x_1` is 1 on `[0, 1/2]` and `1/2` on `[1/2, 3/4]`.

**Step 2 (chain rule and consequences).** For PL homeomorphisms `a, b` and `t ∈ (0,1)`,

`β_{a∘b}(t) = β_a(b(t)) + β_b(t)`.

This holds because `(a∘b)′(t±) = a′(b(t)±)·b′(t±)`, using that `b` is increasing. Three consequences follow.
- (a) `Br(a∘b) ⊆ Br(b) ∪ b⁻¹(Br(a))`, where `Br` is the set of interior breakpoints. With (i) and induction on word
  length, `|Br(h)| ≤ 3|h|` and `|β_h(t)| ≤ |h|` for every `h ∈ F` and every `t`. Here `|h|` is the word length.
- (b) By (ii) and induction, `β_{x_1^k}(1/2) = −k` for all `k ∈ Z`. Negative `k` follows from `x_1^{−k}∘x_1^{k} = id`.
- (c) Put `ĉ_y(t) := β_{y⁻¹}(t)`. Since `(gy)⁻¹ = y⁻¹∘g⁻¹`,

  `ĉ_{gy}(t) = ĉ_y(g⁻¹(t)) + ĉ_g(t)`.

The script checks (a) on all 3957 elements of `B_7` and (c) at 17670 points.

**Step 3 (four words that fix the image of 1/2 and shift the jump).** Let `r ≥ 0` and `p ∈ P(r)`. Choose `h_0 ∈ B_r`
with `h_0(1/2) = p`, and put `j = β_{h_0}(1/2)`. By Step 2(a), `|j| ≤ r`. For `t ∈ {0, 1, 2, 3}` put

`h_t := h_0 ∘ x_1^{−(t−j)}`.

- `h_t(1/2) = h_0(1/2) = p`, because `x_1` fixes `1/2`.
- `β_{h_t}(1/2) = β_{h_0}(1/2) + β_{x_1^{−(t−j)}}(1/2) = j + (t − j) = t`, by Step 2 and 2(b).
- `|h_t| ≤ r + |t − j| ≤ 2r + 3`.

So `g_t := h_t⁻¹ ∈ B_{2r+3}`, with `g_t⁻¹(1/2) = p` and `ĉ_{g_t}(1/2) = β_{h_t}(1/2) = t`. The script verifies this
construction at every `p ∈ P(12)`.

**Step 4 (lamp forcing).** Let `m = 2r + 3`, and suppose `B_n` is 1/2-Ramsey w.r.t. `B_m`. We must show
`n ≥ |P(r)|/12`. If `R(m) = ∞` there is nothing to prove.

Apply Step 0 to

`E := { y ∈ B_n : ĉ_y(1/2) = 0 }`,

and get `ν`. For `y ∈ supp ν` and `g ∈ B_m` we have `gy ∈ B_n`, so `gy ∈ E` iff `ĉ_{gy}(1/2) = 0`. By Step 2(c) and
Step 3, for each `p ∈ P(r)` and each `t ∈ {0, 1, 2, 3}`,

`g_t y ∈ E ⟺ ĉ_y(p) + t = 0`.

Put `q_t := P_ν(ĉ_y(p) = −t) = δ_{g_t}ν(E)`. The four events are disjoint, so `Σ_t q_t ≤ 1` and hence `min_t q_t ≤ 1/4`.
By Step 0, `|q_0 − q_t| ≤ 1/2` for every `t`, so `q_0 ≤ 3/4`. Since `p ∈ (0,1)` (it is the image of `1/2` under a
homeomorphism fixing `0` and `1`), `ĉ_y(p) ≠ 0` means exactly that `p ∈ Br(y⁻¹)`. Therefore

`P_ν(p ∈ Br(y⁻¹)) = 1 − q_0 ≥ 1/4` for every `p ∈ P(r)`.

Summing over `p` gives `E_ν|Br(y⁻¹) ∩ P(r)| ≥ |P(r)|/4`. So some `y ∈ supp ν ⊆ B_n` has `|Br(y⁻¹)| ≥ |P(r)|/4`. By
Step 2(a), `|Br(y⁻¹)| ≤ 3|y⁻¹| = 3|y| ≤ 3n`. Hence `n ≥ |P(r)|/12`. Taking `n = R(m)` proves (a) of the Theorem.

**Step 5 (ping-pong for the Schreier ball).** Put `J = [1/2, 3/4)`, `α = x_1` and `β = x_1∘x_0⁻¹`, so `|α| = 1` and
`|β| = 2`.
- `x_1` maps `[1/2, 3/4)` affinely onto `[1/2, 5/8)`, as `t ↦ t/2 + 1/4`.
- `x_0⁻¹` maps `[1/2, 3/4)` onto `[3/4, 7/8)`, as `t ↦ t/2 + 1/2`.
- `x_1` maps `[3/4, 7/8)` onto `[5/8, 3/4)`, as `t ↦ t − 1/8`.
- So `β(t) = t/2 + 3/8` on `J`, and `β(J) = [5/8, 3/4)`.

Thus `α(J), β(J) ⊆ J` are disjoint. For words `u ≠ v` of the same length `L` in `{α, β}`, `u(1/2) ≠ v(1/2)`. To see
this, strip the longest common prefix `w`, which is a homeomorphism, so it is injective. The remainders `u′, v′` are
nonempty of equal length and start with different letters, so `u′(1/2)` and `v′(1/2)` lie in the disjoint sets
`α(J)` and `β(J)`, because `1/2 ∈ J` and `J` is forward-invariant. Each such word has length at most `2L` in `S ∪ S⁻¹`.
Hence `|P(2L)| ≥ 2^L`, and `|P(r)| ≥ 2^{⌊r/2⌋}` since `P` is nondecreasing in `r`. This is (b). The script confirms the
images of `J` and the `2^L` distinct points for `L ≤ 10`.

**Step 6 (conclusion (c)).** `R(m) ≥ m` is quoted from `moore-ramsey-criterion-for-amenability`. For `m ≤ 2`,
`2^{m/4−6} < 1`. For `m ≥ 3`, let `r = ⌊(m−3)/2⌋ ≥ (m−4)/2`. Since `R` is nondecreasing, (a) and (b) give

`R(m) ≥ R(2r+3) ≥ 2^{⌊r/2⌋}/12 ≥ 2^{r/2 − 1/2}/12 ≥ 2^{m/4 − 3/2 − log₂12} ≥ 2^{m/4 − 6}`. ∎

**Remark 1 (conventions).** If F is written with right actions, so that the product is `y` first, then `g`, the map
`ι: y ↦ y⁻¹`, read from the opposite group into the composition group, is an isomorphism. It sends `S` to `S⁻¹` and
so fixes every ball `B_n` of `S ∪ S⁻¹`. Being 1/2-Ramsey w.r.t. balls is preserved by isomorphisms that fix those
balls, so `R_{F,S}` is the same in both conventions.

**Remark 2 (data).** Exact `|P(r)|` for `r ≤ 12` is `1, 3, 6, 11, 19, 32, 53, 87, 142, 231, 375, 608, 985`, which is
`Fib(r+3) − 2`. The true rate in (a) is therefore about `φ^r/12`. This is only observed; the proof uses `2^{⌊r/2⌋}`.

**Remark 3 (heuristic ceiling of lamp forcing).** Take a coloring defined by the cocycle `ĉ_y` at a finite set `T`
of points, meaning `E` depends only on `(ĉ_y(t))_{t∈T}`. By Step 2(c), `δ_gν(E)` depends only on the law of
`(ĉ_y(g⁻¹t))_{t∈T}`, so balancing constrains `ν` only at the points of `B_m·T`. The resulting lower bound on `n` is at
most `|B_m·T|/3 ≤ |T|·4·3^{m−1}/3`, which is exponential in `m`. Iterating (colorings relative to forced lamps of
shorter words) composes only at the level of radii `r ↦ 2r + 3`, not at the level of `R`. So towers, and in
particular RGAP₂, lie beyond this method. This is an assessment of the method, not a theorem, and it is not part of
the established statement.
