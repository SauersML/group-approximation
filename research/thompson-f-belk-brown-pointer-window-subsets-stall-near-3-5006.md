---
rg: 2
id: thompson-f-belk-brown-pointer-window-subsets-stall-near-3-5006
kind: claim
title: Pointer-window subsets of Belk-Brown forest sets in Thompson's F stall at Cayley density about 3.5006, so neighbour-correlated pointer membership cannot reach the 3.6 that Guba's Q_5 needs
distinct_from:
  thompson-f-product-forest-sets-have-density-below-3-5: that caps product sets (pointer tree independent of its neighbours) at 3.5 by a pen-and-paper min-overlap argument; this treats the survivor it names, sets whose pointer membership depends on a window of neighbouring trees, and finds numerically that the exact optimum over such windows exceeds 3.5 by only about 6e-4.
  thompson-f-guba-q4-systems-have-common-multiples: that turns density above 4 - 2/k into solutions of Guba's Q_k; this is numerical evidence that the pointer-window class, including Guba's own 3.5004 construction, stays far below the 3.6 threshold for Q_5.
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that studies weighted Markov size-chain test vectors for the Rayleigh quotient of ||P||; this studies 0/1 sets for the Cayley density and optimises them exactly by densest-subgraph min cut, not by gradient search.
  thompson-f-is-amenable: that is the open root; this only bounds (numerically) one class of density certificates and decides nothing.
artifacts:
  - experiments/thompson-f-correlated-set-density-2026-09-17/sft_density.py
  - experiments/thompson-f-correlated-set-density-2026-09-17/width3_product.out
  - experiments/thompson-f-correlated-set-density-2026-09-17/bulk_search.py
  - experiments/thompson-f-correlated-set-density-2026-09-17/bulk_search_N4_Np6_s0.out
  - experiments/thompson-f-correlated-set-density-2026-09-17/height_contexts.py
  - experiments/thompson-f-correlated-set-density-2026-09-17/kscan_l2r4.out
  - experiments/thompson-f-correlated-set-density-2026-09-17/k50_l3r3.out
  - experiments/thompson-f-correlated-set-density-2026-09-17/k50_H2J2_l2r3.out
  - experiments/thompson-f-correlated-set-density-2026-09-17/show_removed.py
  - experiments/thompson-f-correlated-set-density-2026-09-17/k50_removed_l2r4.out
  - experiments/thompson-f-correlated-set-density-2026-09-17/tree_contexts.py
  - experiments/thompson-f-correlated-set-density-2026-09-17/exact_trees.out
  - experiments/thompson-f-correlated-set-density-2026-09-17/height_contexts2.py
  - experiments/thompson-f-correlated-set-density-2026-09-17/leafless_k10.out
---

**OPEN** (exact reductions plus exact-optimisation numerics, float64 and int32 min cut; there is no
rigorous ceiling for all windows).

**Claim.** Let `Y ⊂ BB(n, k)` be the Belk–Brown forest set, with trees of height at most `k`. Consider
subsets whose membership is decided by a bounded window of trees around the pointer:

`Y_C = { (T_0..T_{m-1}; i) ∈ BB(n,k) : (c(T_{i-l}), ..., c(T_{i+r})) ∈ C }`,

where `c` is any coarsening of the tree (its height class or its exact type) and `C` is any set of
windows. Then, as `n → ∞` and then `k → ∞`, the density `sup_C δ(Y_C)` converges to about `3.5006`.
This value does not grow with the window width `l + r` or with the number of classes. In particular
this class cannot give density `> 3.6`, and so cannot solve Guba's `Q_5`
(`thompson-f-guba-q4-systems-have-common-multiples`).

**Context.** `thompson-f-product-forest-sets-have-density-below-3-5` proves that product forest sets
have density `< 3.5`, with `3.5` the exact supremum, and names *"Sets where membership of the pointer
tree is correlated with its neighbours"* as the first survivor. This node is that survivor, over the
Belk–Brown bulk.

Guba (arXiv:2210.12304, §3) records the belief that this node tests: "So many people believed that
the va lue 3. 5 for the density of the Cayley graph of F should be optimal." In §5 he beats it by
removing special pointer configurations. There the limit is `(3.5 − 10p)/(1 − 3p) = 3.5 + 0.5p/(1 − 3p)`
with `p = (3/64)(1 − √3/2)^2`, which is `3.500422`. His stated conclusion: "we can reach the density of
ﬁnite subgraphs of the Cayley graph of F in standard generators greater than 3. 5004."

**Setting.** This is the move-graph model of `thompson-f-one-sided-forest-windows-are-norm-lossless`
and `thompson-f-product-forest-sets-have-density-below-3-5`:
- a state is a pointed forest `(T_0..T_{m-1}; i)` with `n` leaves;
- `x_0^{±1}` moves the pointer (a *shift* edge);
- `x_1^{±1}` merges or splits `T_i, T_{i+1}` (a *merge* edge);
- on window sets, the induced Cayley subgraph equals the move graph, and
  `δ(Y) = 2|E(Y)|/|Y|`.

**Exact reductions.**

*(R1) Local limit of `BB(n, k)`.* Fix `k`. As `n → ∞`, the trees around the pointer become i.i.d.,
with law `P(T) = R_k^{|T|}` on trees of height `≤ k`. Here `|T|` is the number of leaves and
`D_k(R_k) = 1`, where `D_0 = x` and `D_h = x + D_{h-1}^2`. This is the renewal limit of step 2 of
`thompson-f-product-forest-sets-have-density-below-3-5`, with `𝒜 = ℬ =` trees of height `≤ k`. The
law of the height `h` is `w_h = D_h(R) − D_{h-1}(R)`.
- Limit weights: `R_k = 1/4 + π²/k² + o(k^{-2})`. The leaf has mass `R_k → 1/4`, and the heights
  `k, k-1, ...` have masses `b_j = t_j − t_{j+1}`, with `t_0 = 1` and `t_j = √(t_{j-1} − 1/4)`. So
  `b_0 = 1 − √3/2`.
- These are the numbers behind Guba's `p = (3/64)(1 − √3/2)^2`.

*(R2) Reduction to a finite weighted densest subgraph.* For a window set `C` of class words of length
`L = l + 1 + r`:
- `|Y_C| = n·w(C)·(1 + o(1))` and `|E(Y_C)| = n·c(E(C))·(1 + o(1))`, up to a common factor. Windows
  that reach past the ends of the forest carry `o(1)` of the mass.
- Vertex weight: `w(v) = Π_j ω(v_j)`, where `ω(c) = Σ_{h ∈ c} w_h`.
- Shift edge `(c_{-l}..c_r) — (c_{-l+1}..c_{r+1})`: weight `Π_{j=-l}^{r+1} ω(c_j)`.
- Merge edge `(.., p, u, c_2, .., c_r) — (.., m, c_2, .., c_{r+1})`: weight
  `Π_{left} ω · W(p,u→m) · Π_{j=2}^{r+1} ω(c_j)`, where
  `W(p,u→m) = Σ_{a∈p, b∈u, 1+max(a,b) ∈ m, ≤ k} w_a w_b`.
  The merged tree `(P, U)` has Boltzmann weight `R^{|P|+|U|} = P(P)P(U)`, so the leaf counts match.
- Self-loops (equal class windows at the two ends) are genuine edges.

So `lim_n δ(Y_C) = 2c(E(C))/w(C)`, and `sup_C` is an exact weighted densest-subgraph problem on
`(#classes)^L` vertices. It is solved by Dinkelbach iteration with Goldberg's min cut
(`sft_density.densest`). The solver was checked against brute force on random 9-vertex graphs.

Consistency check: with `C` = all windows, every run returns exactly `4 − 2R_k`, the Belk–Brown
density. This agrees with the depth-`k` family value in the product node.

*(R3) Removal criterion.* Removing a vertex set `X` from a set of density `δ` raises the density iff
`(Σ_{x∈X} deg(x) − e_in(X)) / w(X) < δ/2`. Here `deg` is the weighted degree and `e_in` the internal
edge weight. So a removal gains only by deleting rare configurations that have low degree relative to
`δ/2 ≈ 1.75`.

Example: the chain fragments `(0 K)^j 0`, where `0` is a leaf and `K` a tree of height `k`, have ratio
`(3j + 2)/(2j + 1) → 3/2 < 1.75`. But their mass decays like `(R·b_0)^j ≈ 0.034^j`. The gain is
bounded by the mass of low-degree fragments, and that mass is geometrically small in the fragment
length.

**Numerical evidence.** Every value is an exact densest-subgraph optimum of the (R2) graph. Min-cut
capacities are rounded to int32, because scipy's `maximum_flow` rejects int64. At the widest windows
this costs up to about `4e-5`, which is small next to the gains measured. Logs are in the artifacts.

| bulk / classes | window `(l, r)` | `4 − 2R_k` (all windows) | best `sup_C δ` | gain |
|---|---|---|---|---|
| height classes `{0}, {1..k-1}, {k}`, `k = 10` | `(2,4)` | `3.415271` | `3.415863` | `5.9e-4` |
| same, `k = 20` | `(2,4)` | `3.469542` | `3.470160` | `6.2e-4` |
| same, `k = 30` | `(2,4)` | `3.484361` | `3.484964` | `6.0e-4` |
| same, `k = 50` | `(2,4)` | `3.493610` | `3.494202` | `5.9e-4` |
| same, `k = 80` | `(2,4)` | `3.497307` | `3.497893` | `5.9e-4` |
| same, `k = 50` | `(3,3)` | `3.493610` | `3.494202` | `5.9e-4` |
| 5 classes `{0},{1},{2..k-2},{k-1},{k}`, `k = 50` | `(2,3)` | `3.493610` | `3.494202` | `5.9e-4` |
| exact tree types, `k = 1` | `(2,3)`, `(4,4)` | `2.763932` | `2.763932` | `0` |
| exact tree types, `k = 2` | `(2,3)` | `3.031943` | `3.031943` | `0` |
| leafless bulk (heights `1..10`), exact heights | `(2,3)` | `2.619721` | `2.983420` | below `3.415` |

Earlier runs in this session, whose logs were not kept, agree with the table:
- at `k = 20`, windows `(2,3)`, `(3,4)`, `(4,5)`, `(5,5)` and a 6-class partition all gave
  `3.470160–3.470163`;
- windows `(0,4)`, `(1,4)`, `(1,5)` gave no gain.

Width-3 windows over product bulks, with an arbitrary pointer context over a free bulk of all trees
with `≤ N` leaves (`sft_density.py`, `width3_product.out`), gave the following:
- the optimum equals `4 − 2R` exactly: `3.116377` at `N = 4` and `3.0` at `N = 3`;
- simulated annealing over nearest-neighbour bulk adjacencies (`bulk_search.py`, 200 + 400 steps)
  never improved on `3.116377`.

**Reading.**
1. *The survivor gains only about `6e-4`.* The gain is flat in `k` (slowly decreasing, `6.2e-4 → 5.9e-4`
   for `k = 20 → 80`). It is also flat in window width and in the number of classes once the window
   contains `(2,3)`. The `k → ∞` extrapolation is `sup ≈ 3.5 + 5.8e-4 ≈ 3.5006`. That is slightly above
   Guba's certified `3.500422`, and about 170 times too small for `Q_5`.
2. *The optimal removal is Guba's fragment.* The removed windows (`k50_removed_l2r4.out`, total mass
   `0.0035`) all contain `0 K 0 K` next to the pointer, where `0` is a leaf and `K` has height `k`. These
   are exactly the special forests of Guba §5 (`T0`, `T2` trivial; `T1`, `T3` of height `k`), with a
   slightly larger family of admissible neighbours. So Guba's construction is essentially the
   pointer-window optimum; it is not a first step of a longer ladder.
3. *Why it stalls* ((R3), heuristic). A fragment that is worth removing must have boundary-to-mass
   ratio below `δ/2 ≈ 1.75`. Leaves and height-`k` trees are the only low-degree ingredients. Their
   alternation has ratio `→ 3/2`, but its mass is `≈ 0.034^j`. The ratio never goes below `3/2`, so no
   long, cheap fragment exists.
4. *Changing the bulk does not help.* The leafless periodic bulk (the second survivor of the product
   node) is worse than Belk–Brown at the same `k`. Exact tree types at small `k` give no gain at all.

**Class (numerically) killed as a route to `Q_5`:** subsets of Belk–Brown sets cut out by any
bounded pointer window of height classes.
- *Invariant.* The local-limit window law (R1). It is a product of the height masses
  `w_h(R_k)`, with the leaf mass pinned to `R_k ≥ 1/4`. This is the same `1/4` as Guba's
  `|BB(n−1,k)|/|BB(n,k)| ≥ 1/4` heuristic.
- *Where every member dies.* At the (R3) removal step: the only fragments with ratio below `δ/2` are
  leaf/height-`k` alternations, with ratio `≥ 3/2` and mass `≤ 0.034^j`. So the density gain is at most
  a constant of order `10^{-3}`.

**Not covered.**
- A rigorous version of the ceiling. It needs a dual certificate (a fractional orientation with max
  load `≤ 1.7503`) valid for all `l, r` uniformly. The min cut at the final Dinkelbach step certifies
  each finite `(k, classes, l, r)` instance only, up to rounding.
- Membership that depends on unbounded windows, or on global statistics of the forest: for example,
  hierarchical or multi-scale conditions, which Moore's tower bound suggests are needed.
- Bulks that are not Belk–Brown and not leafless-periodic. Only small random nearest-neighbour bulks
  were searched.
- Sets not of window form in the lossless model, i.e. sets that are not unions of pointed-forest
  windows.

## Attempts

- **Exact densest-subgraph search over pointer windows (swarm-0917-w17-w17-f-break, 2026-09-19,
  belief-breaker, computation).**
  - *Done:* (R1)–(R3); the table.
  - *Dies at:* a uniform-in-width upper certificate. The finite instances are exact, but an LP dual
    uniform in `l, r` was not constructed.
  - *Next falsifiable step:* a two-level condition, a pointer window whose admissible set depends on a
    coarse statistic (for example, the number of height-`k` trees in a block of length `B ≫ r`). This
    tests whether non-local correlation breaks the `3/2` fragment floor.
