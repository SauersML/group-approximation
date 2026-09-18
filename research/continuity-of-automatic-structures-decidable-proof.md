---
rg: 2
id: continuity-of-automatic-structures-decidable-proof
kind: route
title: Bounded length difference by pumping, then run two copies of the multiplier automaton on a common input and pump a cycle after the outputs split
target: continuity-of-automatic-structures-is-decidable
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

Notation as in the target. Put `Q = Q_s` and `q_0` for the initial state. We assume the
automaton accepts only well-formed paddings: once a tape reads `$`, it reads only `$`.
This is the usual convention for synchronous acceptors.

**Step 0 (bounded length difference).** `||f_s(β)| − |β|| < |Q|` for every `β`.
- Suppose `|α| ≥ |β| + |Q|` with `α = f_s(β)`. The accepting run on `(α, β)` reads at
  least `|Q|` letters of the form `(a, $)` after `β` ends. So it repeats a state there.
- Pumping that loop gives an accepted pair `(α*, β)` with `α* ≠ α`. This contradicts the
  fact that `R_s` is the graph of a function.
- If instead `|β| ≥ |α| + |Q|`, the same argument gives an accepted `(α, β*)` with
  `β* ≠ β`. This contradicts injectivity of `f_s`: left multiplication is a bijection and
  `L` is a normal form.

**Step 1 (3 ⇒ 2).** Suppose there is no split cycle. Let `|β ∧ β'| ≥ i + K` with
`K = |Q|^2`, and suppose `|f_s(β) ∧ f_s(β')| < i`.
- Run `𝒜_s` on `(f_s(β), β)` and on `(f_s(β'), β')` for the first `i + K` steps. The
  `b`-letters agree and lie in `X`. So this is a path in the twin graph.
- It splits at some position `j ≤ i`, where the outputs first differ.
- The segment from `j` to `i + K` has `K` edges, so it repeats a vertex of `Q × Q`, which
  gives a cycle after the split.
- Both runs go on to accept, so the endpoint is a pair of co-accessible states. This is a
  split cycle, a contradiction.

**Step 2 (2 ⇒ 1).** Take `M = N + K`.

**Step 3 (1 ⇒ 3).** Suppose a split cycle exists. It first splits at position `j`, then
runs a cycle of length `ℓ`, then reaches a co-accessible pair `(p, p')`.
- Traverse the cycle `r` times and complete from `p` and from `p'` to acceptance.
- This gives accepted pairs `(α_r, β_r)` and `(α'_r, β'_r)`, with `β_r` and `β'_r`
  agreeing on at least `j + rℓ` letters.
- The outputs `α_r` and `α'_r` differ at or before position `j`. If one of them has
  already stopped there, then they differ in length by that position.
- So `|f_s(β_r) ∧ f_s(β'_r)| < j` while `|β_r ∧ β'_r| → ∞`, and continuity fails with
  `N = j`.

**Decidability.** Everything used is a finite search on known finite automata:
- the vertices reachable from `(q_0, q_0)`;
- which of them are reached by a split path;
- the cycles of the twin graph;
- the co-accessible states of `𝒜_s`.

The automata `𝒜_s` of an automatic structure are part of its data. □
