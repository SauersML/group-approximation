# Deep promotion as multi-type bootstrap percolation, and why the (W) counting argument cannot bound it

swarm-0917-w20-w20-fp-break, belief breaker, 2026-09-20. Target:
`fpbs-mal-overfold-merges-never-help` (O). Family: operator-algebras / spectral.
Scripts: `experiments/fpbs-overfold-spectral-percolation-2026-09-17/`.

**Question.** Can the mechanism that proves (W) (`fpbs-mal-twisted-level-seed-density-random-lift-proof`,
Lemma 1 closure counting + Lemma 2 expander mixing + strong convergence) be run directly on `deep_j`,
bypassing (O)? That would give the floor without the exchange statement.

**Answer: no, already at `j = 1`, and not by a lossy constant.** Every argument of the form
"a closure stage `C` has at least `|C| − |S|` full hyperedges (Lemma 1), and every set of that size has
fewer" is contradicted by explicit sets of every scale that have **more** full hyperedges than atoms,
even with an optimal choice of type weights. (O) stays OPEN; this closes one route to the floor around it.

## 1. Exact model (proved; checked by `hyper.py`)

Pullback form (proved in the target): a same-fibre pair of `Γ_{j+1}(Q)` is `(q; c, c')`, `c ≠ c'` in
`V(C_{j+1})`. The fold closure of a seed family is the least family of fibre equivalence relations
closed under (i) propagation `c E_q c' ⇒ cx E_{qx} c'x` and (ii) transitivity inside each fibre.

- **Atoms.** Propagation classes. The off-diagonal pair graph `C_{j+1} ×_R C_{j+1}` has components
  (pair types) that are finite trees (malnormality). So every propagation class is a copy of a type tree
  `P_i` rooted at `(x, root_i)`: atom `(x, i)`, `x ∈ Q`. Atoms: `Q × [R]`.
- **Hyperedges.** Transitivity acts on triples `{c, d, e}` of distinct vertices in one fibre. The
  distinct-triple graph of `C_{j+1}` has components (triangle types), all finite trees too (checked);
  all triples of one component give the same implication. Triangle type `k` at `q` is the hyperedge
  `{(q g_{k,1}, i_{k,1}), (q g_{k,2}, i_{k,2}), (q g_{k,3}, i_{k,3})}`.
- **Closure = 2-of-3 bootstrap percolation** on this 3-uniform hypergraph; the goal is every atom of
  the lawful type. So `deep_j(Q)` is the least percolating-to-lawful seed set, `law_j` the same with
  lawful seeds only (only the one `LLL` hyperedge type then matters: it is the triple
  `(y, y a^{-1}, y t_j^{-1})` of the (W) proof).
- Hyperedge types never have composition `LLO` (Lemma A of the census artifact: two lawful pairs
  force a lawful third).

| `j` | pair types `R` | triangle types | `LLL` | `LOO` | `OOO` |
|---|---|---|---|---|---|
| 0 | 1 | 1 | 1 | 0 | 0 |
| 1 | 12 | 42 | 1 | 23 | 18 |
| 2 | 88 | 836 | 1 | 153 | 682 |

`hyper.py` validates the model against the true fold closure `pb.Level.closure` on random levels
(`j = 0, n = 7`; `j = 1, n = 6, 9`; `j = 2, n = 5`; 20 random seed sets each, every same-fibre pair
compared): 0 mismatches.

## 2. The spectral relaxation fails by a factor of 4 (`spectral.py`, `spectral_out.txt`)

Generalise Lemma 2. Bound each full hyperedge by a convex combination of its three pair counts, with
weights `1/3`. Then `F(A) ≤ <1_A, P 1_A>`, where `P = sym Σ_{k,p} c_{k,p} E_{i,i'} ⊗ U_g` acts on
`ℓ²(Q) ⊗ C^R`. Splitting off the constants gives
`F(A) ≤ n αᵀBα + λ n Σ α_i(1−α_i)`, with `λ = ‖P|ℓ²_0 ⊗ C^R‖`.

| | `j = 0` (the (W) case) | `j = 1` |
|---|---|---|
| pair-weight per atom type (row sums of `B`) | 1 | 2 to 8.67 (lawful: 8.67) |
| `λ`, random level, `n = 3000` | 0.834 | 3.548 |
| slack `μ − sup_α(...)` at `μ = 0.5` | +0.041 | −1.29 |

The argument needs `λ < 1`. At `j = 1` the average pair-weight per atom type is `2·42/12 = 7` for every
choice of convex weights. Section 3 shows that the failure is intrinsic, not an artefact of the
relaxation.

## 3. Class kill: sets with more full hyperedges than atoms, at every scale

For a set `A` of atoms, `F(A)` is the number of hyperedges with all three atoms in `A`.

**Proposition K (proved by finite computation).** At `j = 1`, let `B_r` be the radius-`r` ball of the
Cayley tree of `F(a,b)`. Then `F(B_2 × [R]) = 226 > 204 = |B_2 × [R]|`.

`tree_count.py` computes this exactly over reduced words: `(q, k)` counts iff all three `q g_{k,p}` have
length `≤ r`, where `q` ranges over all words of length `≤ r + max|g|`. Output: `tree_count_out.txt`.

| radius `r` | 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| `j = 1`: `F/|A|` | 0.833 | 1.108 | 1.197 | 1.225 |
| `j = 0`: `F/|A|` | 0.200 | 0.294 | 0.321 | 0.329 |

At `j = 2`, radius 2 gives `F/|A| ≥ 3.21` on tree-shaped balls of a random level (`balls.py`,
`balls_out.txt`).

**Transfer to levels.** Let `ℓ = max |g_{k,p}|`.
- If the radius-`(2 + ℓ)` neighbourhood of `x ∈ Q` is tree-shaped, then `F(B_2(x) × [R]) = 226`.
- For pairwise disjoint balls, `F(∪_c X_c × [R]) ≥ Σ_c F(X_c × [R])`, since no hyperedge lies inside
  two disjoint blocks.
- Every essentially free profinite tower is Benjamini–Schramm convergent to the Cayley tree, so this
  covers every candidate witness tower of the floor route. In such a tower, all but `o(n)` points have
  tree-shaped neighbourhoods of any fixed radius.
- Pack balls greedily, with centres at mutual distance `≥ 5`, avoiding the `o(n)` bad points. Every
  point is then within distance 4 of a centre, so the packing covers at least `(17/161 − o(1)) n`
  points. That makes `|A|` up to about `1.27 n`, in steps of 204.
- Random level, `n = 40000`: 966 disjoint tree-shaped radius-2 balls, each block with `F ≥ 226`. The
  union has `|A| = 4.93 n` and `F/|A| = 1.1085`.

**Consequence (the kill).** Consider any lower bound on `deep_j` of the form: Lemma 1 at a stage of
size `m`, then `|S| ≥ m − sup_{|A|=m} F(A)`.
- For every `m` between `O(1)` and `1.27 n`, that bound is at most 0. So on every locally tree-like
  tower it proves only `deep_1 ≥ O(1)`.
- The argument may only use `m ≤ n`, because the closure is guaranteed to reach just the `n` lawful
  atoms.
- Mixing and strong convergence cannot repair it: the extremal sets are local and tree-shaped. This is
  the exact point where (W)'s Lemma 2 dies, for all `j ≥ 1`.

**Weighted variant, also dead (`weighted_lp.py`, `weighted_lp_j1_r3.txt`).**
- Give atom type `i` weight `w_i ≥ 0`, with `w_lawful = 1`. Each step activates an atom of weight at
  most `W(h) = max_{a∈h} w(a)`, through a distinct full hyperedge `h`. So
  `w(C) − w(S) ≤ Σ_{h ⊆ C} W(h)`.
- The LP computes `t* = min_w max_{blocks B_r × I} (weighted excess per ball point)`, over all `2^12`
  type sets `I`:
  - `r ≤ 2`: `t* = 1.294`;
  - `r ≤ 3`: `t* = 2.358`.
- In both cases the optimum is at equal weights. Every weighting therefore has a block whose weighted
  full-hyperedge count exceeds its weighted size.
- Counting only lawful activations, `w_O = 0`, is worse: the 24 `LLL` and `LOO` types become free
  to fill.

## 4. What this changes

- **Why (W) works and deep does not follow.** With lawful atoms only, the hypergraph is locally
  subcritical. In the tree, `F/|A| → 1/3` (the lawful hyperedges form a linear hypertree), and
  expander mixing converts the global balance `F(Q) = n` into a gap. Overfold types make it locally
  **supercritical**: `F/|A|` is above 1 already at radius 2, and grows with `j` (about 1.23 at `j = 1`,
  at least 3.2 at `j = 2`). So no uniform-in-`j` density or counting argument exists, not even at a
  single `j ≥ 1`.
- **What any proof of the floor must use.** Something that tells reachable closure stages apart from
  arbitrary dense sets: which atoms a stage can actually activate, in what order. Examples are (O)
  itself, (O-step), or (RI) and (E(2)) of the w19 minimal-counterexample artifact. Counting full
  hyperedges is provably not enough.
- **Not refuted.** The ball blocks are not shown to be cheaply percolable. Heuristically their local
  supercriticality is the only mechanism by which overfold seeds could beat `law`, and the random
  cascades (`fpbs-overfold-cascade-2026-09-19.md`) show it does not trigger from random seeds. (O)
  stays OPEN, and the floor route still needs it.
- **New exact facts, reusable.**
  - Triangle types are finite trees, since distinct-triple components have no core.
  - There is no `LLO` hyperedge type.
  - Counts: 1/42/836 triangle types at `j = 0/1/2`.
  - `hyper.py` gives a fast, validated bootstrap model of `deep_j` for large levels:
    `12n` atoms and `42n` hyperedges at `j = 1`.
