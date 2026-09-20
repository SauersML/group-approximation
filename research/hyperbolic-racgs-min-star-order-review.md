---
rg: 2
id: hyperbolic-racgs-min-star-order-review
kind: claim
title: Referee review of 3b86cb5549 (every non-elementary hyperbolic RACG, and its commensurability class, is a contracting RSG) — the cone-vertex splitting, the corrected "every simplex is a state" (r ∉ St(s) suffices), Lemma K and the reachability induction are all correct; the resulting state graph is strongly connected and not a cycle, which is exactly the (IRR) criterion the refereed spread-nerve proof used; the hexagon-disk example and its bad order check
distinct_from:
  hyperbolic-racgs-contracting-rsg-via-min-star-order: that is the lane proof under review; this checks it line by line against the refereed spread-nerve proof.
  hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof: that is the refereed proof under the spread condition (a); this confirms the new proof reuses its Steps 1, 2 and 4 legitimately and reaches the same (IRR) criterion without (a).
  kourovka-18-48-d-adic-review: that reviews the 18.48 node; this reviews the RACG node.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of `hyperbolic-racgs-contracting-rsg-via-min-star-order` and
`hyperbolic-racgs-are-contracting-rsgs` in 3b86cb5549, lane bh-q11-beyond).** Verdict: **PASS.**
- All six required nodes are ESTABLISHED on main.
- I found no prior statement: a web search on rational similarity groups and right-angled Coxeter groups came up
  empty, which agrees with the earlier searches recorded in the spread-nerve review.

## Step 0: splitting off cone vertices is correct

- **The join.** Cone vertices are pairwise adjacent, so by flagness they span a simplex `Δ`. Then `L = L_0 ∗ Δ` and
  `W = W_(L_0) × (Z/2)^(|Δ|)`.
- **`L_0` has no cone vertex.** A cone vertex of `L_0` would be adjacent to all of `L`, so it would lie in `Δ`.
- **`L_0` keeps the hypotheses.** It is an induced subcomplex, so it has no induced 4-cycle. `W_(L_0)` has finite
  index in `W`, so it is non-elementary, and `|S_0| ≥ 3`.
- **The transfer** uses the ESTABLISHED products-with-finite-groups node. Commensurability classes agree.

## Step 1: what is inherited, and the corrected state lemma

- **`𝒩` is connected.** Otherwise `L` is a join. If neither factor is a simplex, two non-adjacent pairs give an
  induced 4-cycle. A simplex factor consists of cone vertices. Correct.
- **Inherited steps.** Steps 1, 2 and 4 of the spread-nerve proof use (a) only through "no cone vertex", together
  with (H). This covers (NA), the trivial finite radical, faithfulness (where `u ∉ St(t)` needs only that `t` is not
  a cone vertex), and the transition rule. Irreducibility of `W` follows from connectivity of `𝒩`.
  - **The transition rule holds for every total order.** Its derivation (Step 4 there, and Step 1 of
    `greedy-cube-codings-rsg-proof`) uses only `s_0 = min σ` for the fixed order. That order is arbitrary and
    `W`-equivariant through the edge labels. It never uses a special order.
- **Every nonempty simplex is a state, with `r ∉ St(s)` only.** Check the word `w_σ(rs)^∞` by Tits's criterion:
  - The two occurrences of `s` are separated by `r`, which does not commute with `s`.
  - Consecutive `r`'s are separated by `s`.
  - The letters of `σ ∖ {s}` occur once, and `r ∉ σ ⊆ St(s)`.
  - Left descents: each letter of `σ` is preceded only by commuting letters of `σ`. Every `r` is preceded by an `s`,
    and every later `s` by an `r`.
  - So the descent set is exactly `σ` at every stage. The earlier proof's `r ∉ ⋃ St(s′)` was more than needed.
    Correct.

## Lemma K is correct

Suppose every `o ∈ O(u_1)` is adjacent to `t`. Take `z` not adjacent to `t`; it exists because `t` is not a cone
vertex.
- `z ∉ O(u_1)` by the assumption, and `z ≠ u_1`, so `z ∈ lk(u_1)`.
- If `z` had a neighbour `o ∈ O(u_1)`, the cycle `u_1 z o t` would be a 4-cycle on four distinct vertices. Both
  chords are absent: `u_1 o` because `o ∉ St(u_1)`, and `zt` by the choice of `z`. That is against (H).
- So `St(z) ⊆ St(u_1)`, and `t ∈ St(u_1) ∖ St(z)`, which contradicts minimality.
- (H) is used exactly once, as the node says.

## Step 3, the (IRR) reachability argument, checked closely

The transition rule used is: `σ → τ` iff `s_0 = min σ ∉ τ` and `τ ∩ lk(s_0) = σ ∖ {s_0}`, with every nonempty
simplex a state.

- **Predecessors through `u_1`, for `τ ∌ u_1`.** `P(τ) = {u_1} ∪ (τ ∩ lk(u_1))` is a clique, hence a simplex. Its
  minimum is `u_1`, the global minimum. `u_1 ∉ τ`, and `τ ∩ lk(u_1) = P(τ) ∖ {u_1}`. So `P(τ) → τ`.
- **Claim A (`τ ∋ u_1`), by induction on `|τ|`.**
  - Set `T = τ ∖ {u_1} ⊆ lk(u_1)`, pick `t ∈ T`, and let Lemma K give `o ∈ O(u_1)` not adjacent to `t`.
  - `ρ = {o} ∪ (T ∩ lk(o))` is a simplex. Its minimum is `o`, because `o` lies in the middle block and
    `T ⊆ lk(u_1)` lies in the top block.
  - `o ∉ τ ⊆ St(u_1)`. Also `τ ∩ lk(o) = T ∩ lk(o)`, since `u_1 ∉ lk(o)`, and that equals `ρ ∖ {o}`. So `ρ → τ`.
  - `u_1 ∉ ρ`, and `ρ ∩ lk(u_1) = T ∩ lk(o)`, since `o ∉ lk(u_1)`. So `P(ρ) = {u_1} ∪ (T ∩ lk(o))`.
  - `P(ρ)` is a proper subset of `τ`, since `t ∉ lk(o)`, and it contains `u_1`. So it is good by induction, and
    the path `(singleton) ⇝ P(ρ) → ρ → τ` exists. Correct.
- **Claim B** follows from Claim A and `P(τ) → τ`. Correct.
- **Where the order matters.** It enters in exactly two places: `min P(τ) = u_1`, and `min ρ = o`. The three-block
  order `u_1 < O(u_1) < lk(u_1)` is what makes both hold.

## Step 4: (IRR), matching the refereed definition

- **Strong connectivity.**
  - `σ → σ ∖ {min σ}` for `|σ| ≥ 2`.
  - `{s} → {t}` iff `t ∉ St(s)`, so the singletons are strongly connected through the connected `𝒩`.
  - With Step 3, the whole graph is strongly connected.
- **Branching.** Branching fails only if `𝒩` is a perfect matching, which is impossible for a connected `𝒩` on
  `≥ 3` vertices. So the graph is not a single cycle.
- **The criterion.** "Strongly connected and not a cycle" is exactly the criterion of Step 5 of the refereed
  spread-nerve proof. The conclusion goes through `sft-irreducible-core-iff-unique-recurrent-component` in the same
  way, whose hypotheses (no empty cones, no isolated points) hold here. Only the proof of "singletons reach every
  simplex" changed, and it no longer uses (a). So (IRR) is **the same property**, reached without the spread
  condition.

## Step 5: finite-index and commensurable groups are correct

- **The odd loop when `u_1` has a neighbour `t`.** `{o} → {u_1,t}` holds because `o` is adjacent to neither.
  `{u_1,t} → {t}` drops the minimum `u_1`. `{t} → {o}` holds because `o ∉ St(t)`. That is length 3.
- **The other cases.** An isolated `u_1` with an edge `{t,t′}` works the same way. With no edges, `𝒩` is complete.
- **The loop group.** Loops generating `W⁺` need only connectivity of `𝒩`, as refereed. So the loop group is `W`,
  and the loop and overgroup nodes apply.

## The hexagon disk: checked

- **The complex.**
  - The links of `a` and `b` are the 5-cycles `b c_1 y_1 y_2 c_2` and `a c_1 x_1 x_2 c_2`.
  - The boundary is the hexagon `y_1 c_1 x_1 x_2 c_2 y_2`.
  - Every 3-clique is one of the eight listed triangles, so the complex is flag.
  - I found no induced 4-cycle: `c_1 a c_2 b` has the chord `ab`, and the other 4-cycles all pass through `a` or `b`
    together with two of their neighbours, which are adjacent.
  - There is no cone vertex.
- **Spreadness fails at `{a,b}`**: `St(a) ∪ St(b) = S`.
- **The minimal star.** `St(y_1) = {y_1, c_1, a, y_2}` is inclusion-minimal, because every vertex has degree `≥ 3`.
  `O(y_1) = {b, c_2, x_1, x_2}`, as stated.
- **The bad order.** With `c_1, c_2 < a, b < …`:
  - `{a,b,c_1} → {a,b,c_2}` holds: the minimum is `c_1`, and `{a,b,c_2} ∩ lk(c_1) = {a,b}`. The reverse edge
    holds symmetrically.
  - `{a,b,c_2}` is the **only** predecessor of `{a,b,c_1}`. The other candidates, from `y_1, x_1, y_2, x_2`, would
    need `y_1 < c_1`, `x_1 < c_1`, `y_2 < a` or `x_2 < b`, and all four fail.
  - So this 2-cycle is a second recurrent component, and (IRR) fails for that order. Correct.

## Bottom line

This settles BBMZ Question 1.1 for every non-elementary hyperbolic right-angled Coxeter group and its
commensurability class, with no condition on the nerve. The new ingredients are:
- the minimal-star order;
- Lemma K;
- the corrected state lemma.

The (IRR) conclusion is the one the refereed proof used. The status line of
`hyperbolic-racgs-are-contracting-rsgs` can cite this review. The remaining parts of Question 1.1 are as the node
lists them.
