---
rg: 2
id: hyperbolic-racgs-contracting-rsg-via-min-star-order
kind: route
title: Split off cone vertices, order the generators from a vertex of inclusion-minimal star, and show every simplex is reachable from a singleton in the greedy state graph
target: hyperbolic-racgs-are-contracting-rsgs
requires:
  - greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs
  - hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs
  - contracting-rsgs-closed-under-products-with-finite-groups
  - contracting-rsgs-closed-under-finite-index-overgroups
  - contracting-rsgs-pass-to-finite-index-subgroups-via-loops
  - sft-irreducible-core-iff-unique-recurrent-component
---

**Lane proof** (lane `bh-q11-beyond`, 2026-09-19), elementary, **not independently reviewed**. Notation as in
`hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof`: `St(s)` is `s` with its neighbours, `lk(s) = St(s) ∖ {s}`,
and `𝒩` is the complement graph on `S`. For `u ∈ S` write `O(u) = S ∖ St(u)`.

## Step 0: reduction to the cone-free case

- **Cone vertices form a join factor.** Let `Δ` be the set of vertices adjacent to every other vertex. Any two of them are
  adjacent, so `Δ` is a simplex (flag), and `L = L_0 ∗ Δ` with `L_0 = L ∖ Δ`. Hence `W = W_{L_0} × (Z/2)^{|Δ|}`.
- **`L_0` has no cone vertex.** A cone vertex of `L_0` is adjacent to all of `L_0` and to `Δ`, so it would lie in `Δ`.
- **`L_0` is still large.** `W` is non-elementary, and `W_{L_0}` has finite index in `W`, so `W_{L_0}` is non-elementary.
  With at most 2 vertices `W_{L_0}` is finite or `D_∞`, so `|S_0| ≥ 3`.
- **Transfer.** If `W_{L_0}` is a contracting RSG, so is `W`, by `contracting-rsgs-closed-under-products-with-finite-groups`.
  A group commensurable with `W` is commensurable with `W_{L_0}`. So it suffices to prove items 1 and 2 for `W_{L_0}`.

From now on `L` has no cone vertex, `|S| ≥ 3`, and `L` has no induced 4-cycle **(H)**.

## Step 1: what carries over unchanged

- **`𝒩` is connected.** If not, the components partition `S` into `V_1, V_2` with every vertex of `V_1` adjacent to every
  vertex of `V_2`, so `L = L[V_1] ∗ L[V_2]` (flag). If neither factor is a simplex, two non-adjacent pairs give an induced
  4-cycle, against (H). A simplex factor consists of cone vertices, which do not exist.
- **Steps 1, 2 and 4 of `hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof`** (referee PASS) use only (H) and
  "no cone vertex". These are (NA), trivial finite radical, faithfulness on `∂W`, and the transition rule:
  `σ → τ` exactly when `s_0 = min σ ∉ τ` and `τ ∩ lk(s_0) = σ ∖ {s_0}`. The rule holds for **every** total order on `S`.
- **Every nonempty simplex is a state** (a correction of that proof's Step 3, which used more than it needed).
  - Given `σ` and any `s ∈ σ`, pick `r ∉ St(s)`; it exists because `s` is not a cone vertex, and `r ∉ σ`.
  - The word `w_σ(rs)^∞` is reduced: the two `s`'s are separated by `r`, which does not commute with `s`, and the letters
    of `σ ∖ {s}` occur once.
  - Its left descents are exactly `σ`. The first `r` is preceded by `s`, and every later letter is preceded by `r` or `s`,
    neither of which commutes with it. So `r` need not avoid the other stars, only `St(s)`.

## Step 2: the order and the key lemma

- **Choice.** Let `u_1 ∈ S` have `St(u_1)` minimal under inclusion among all vertex stars. Fix a total order with
  `u_1 < o < t` for all `o ∈ O(u_1)` and all `t ∈ lk(u_1)`, arbitrary inside `O(u_1)` and inside `lk(u_1)`.
  `O(u_1) ≠ ∅`, since `u_1` is not a cone vertex.
- **Lemma K.** For every `t ∈ lk(u_1)` there is `o ∈ O(u_1)` not adjacent to `t`.
  - Suppose every `o ∈ O(u_1)` is adjacent to `t`. Since `t` is not a cone vertex, some `z ≠ t` is not adjacent to `t`.
    Then `z ∉ O(u_1)`, and `z ≠ u_1` since `t ∈ lk(u_1)`, so `z ∈ lk(u_1)`.
  - If `z` were adjacent to some `o ∈ O(u_1)`, then `u_1 – z – o – t – u_1` would be a 4-cycle. Its chords `u_1o` (since
    `o ∉ St(u_1)`) and `zt` are both absent, so it would be induced, against (H).
  - So every neighbour of `z` lies in `St(u_1)`, and `St(z) ⊆ St(u_1)`. Also `t ∈ St(u_1) ∖ St(z)`. So
    `St(z) ⊊ St(u_1)`, against minimality. ∎

## Step 3: every simplex is reachable from a singleton

Call a nonempty simplex **good** if some directed path in the state graph runs from a singleton to it.

- **Predecessor through `u_1`.** If `u_1 ∉ τ`, put `P(τ) = {u_1} ∪ (τ ∩ lk(u_1))`. It is a simplex (flag), its minimum is
  `u_1`, `u_1 ∉ τ`, and `τ ∩ lk(u_1) = P(τ) ∖ {u_1}`. So `P(τ) → τ` by the transition rule.
- **Claim A: every simplex `τ ∋ u_1` is good.** Induction on `|τ|`. If `τ = {u_1}`, it is a singleton. Otherwise let
  `T = τ ∖ {u_1} ≠ ∅`, so `T ⊆ lk(u_1)`. By Lemma K, applied to any `t ∈ T`, there is `o ∈ O(u_1)` with `t ∉ lk(o)`.
  - Put `ρ = {o} ∪ (T ∩ lk(o))`, a simplex. Its minimum is `o`, because `T ⊆ lk(u_1)` sits above `O(u_1)` in the order.
    Also `o ∉ τ`, and `τ ∩ lk(o) = T ∩ lk(o) = ρ ∖ {o}`, since `o` is not adjacent to `u_1`. So `ρ → τ`.
  - `u_1 ∉ ρ`, so `P(ρ) = {u_1} ∪ (ρ ∩ lk(u_1)) = {u_1} ∪ (T ∩ lk(o))` and `P(ρ) → ρ`.
  - `P(ρ) ⊊ τ`, because `t ∈ T ∖ lk(o)`. It contains `u_1`, so it is good by induction, and so is `τ`. ∎
- **Claim B: every simplex `τ ∌ u_1` is good**, since `P(τ) → τ` and `P(τ) ∋ u_1` is good by Claim A. ∎

## Step 4: (IRR)

- **Every simplex reaches a singleton**: `σ → σ ∖ {min σ}` whenever `|σ| ≥ 2`.
- **The singletons are strongly connected**: `{s} → {t}` iff `t ∉ St(s)`, i.e. iff `st` is an edge of `𝒩`, which is
  connected by Step 1.
- **So the whole graph is strongly connected**, by Step 3.
- **Branching.** If every singleton had a single successor among the singletons, `𝒩` would be a perfect matching; being
  connected it would be one edge, so `|S| = 2`. So the graph is not a single cycle.
- By `sft-irreducible-core-iff-unique-recurrent-component`, (IRR) holds. With (NA), trivial finite radical and the free
  vertex action, `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs` gives item 1.

## Step 5: finite-index subgroups and commensurable groups

Follow Step 6 of `hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof`, with its two inputs re-proved here.
- **Loops at a singleton generate `W⁺`.** This uses only the connectivity of `𝒩` (Step 1).
- **An odd loop exists.**
  - *If `u_1` has a neighbour `t`:* Lemma K gives `o ∈ O(u_1)` with `o ∉ St(t)`. Then
    `{o} → {u_1, t} → {t} → {o}`, since `{u_1,t} ∩ St(o) = ∅`, `u_1` is the minimum, and `o ∉ St(t)`. The label `o u_1 t`
    has length 3.
  - *If `u_1` is isolated and `L` has an edge `{t,t'}`:* the loop `{u_1} → {t,t'} → {max} → {u_1}` works.
  - *If `L` has no edge:* `𝒩` is complete on `≥ 3` vertices and has a triangle.
- So the loop group acts transitively on `Γ∖W` for every finite-index `Γ`. By
  `contracting-rsgs-pass-to-finite-index-subgroups-via-loops`, `Γ` is a contracting RSG. Commensurable groups follow from
  `contracting-rsgs-closed-under-finite-index-overgroups`. ∎

## For the referee

- The new material is Step 0, Step 1's third bullet, Lemma K and Step 3. Everything else is quoted from refereed nodes.
- Lemma K is the only place (H) enters the new part, and it enters exactly once.
- Please check that the transition rule quoted in Step 1 really holds for an arbitrary total order. The earlier proof fixes
  "a total order on S" and never uses a special one; its Step 4 derivation is order-free.
- **Worked example** (see the claim): the hexagon disk, where (a) fails at `{a,b}` and `{a,b,c_i}`, the minimal star is
  `St(y_1)`, and a bad order (`c_1, c_2` below `a, b`, below everything else) yields the extra recurrent component
  `{a,b,c_1} ⇄ {a,b,c_2}`.
