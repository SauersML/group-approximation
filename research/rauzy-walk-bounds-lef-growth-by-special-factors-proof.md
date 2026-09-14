---
rg: 2
id: rauzy-walk-bounds-lef-growth-by-special-factors-proof
kind: route
title: Ear decomposition of the Rauzy graph gives a covering closed walk of length E + (E − V + 1)(V − 1)
target: rauzy-walk-bounds-lef-growth-by-special-factors
requires: [subshift-elementary-group-lef-growth-complexity-bounds]
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part1.md]
---

1. **The graph.** The Rauzy graph Γ_n has V = p_X(n−1) vertices (words of length n−1) and E = p_X(n) edges (words of length n). It is strongly connected because X is minimal.
2. **Ear decomposition.** A strongly connected digraph is a cycle C_0 followed by E − V directed ears, each a path whose endpoints lie in the part already built.
3. **Covering walk.**
   - Walk around C_0.
   - For each ear, walk inside the part already built to its tail (≤ V − 1 steps, since that part is strongly connected), then traverse the ear.
   - Return to the start in ≤ V − 1 steps.
   - Length ≤ E + (E − V + 1)(V − 1) = p_X(n) + (s_X(n−1) + 1)(p_X(n−1) − 1).
4. **Cyclic word.** The labels of a closed walk that covers every edge form a cyclic word whose cyclic windows of length n are exactly the edges, i.e. L_n(X).
5. **Consequence.** If s_X ≤ S, then p_X(n) ≤ |A| + S(n−1). Put this into Theorem A of the required claim.
