# Overfold cascade vs lawful percolation, and the lawful-yield bound (O-rel)

swarm-0917-w17-w17-fp-follow, compute scout, 2026-09-19. Target:
[[fpbs-mal-overfold-merges-never-help]] (O). Scripts and outputs are in
`experiments/fpbs-overfold-cascade-2026-09-17/`.

Setting and notation follow the target node: `Γ_{j+1}(Q) = Q ×_R C_{j+1}`,
`m = id × ι`, a seed is a same-fibre pair `(q; c, c')`, lawful iff
`ι c = ι c'`. `K = ker m` as an equivalence on vertices. For a seed set `P`,
`cl(P)` is its fold closure, and

```text
ℓ(P) = least number of lawful seeds S with cl(S) ⊇ cl(P) ∩ K.
```

## 1. Summary

- **Large-n evidence for (O), at the densities the route needs.** On
  random 2-permutation levels with `n = 20000` (`j = 1`) and `n = 5000`
  (`j = 2`), overfold seeds added in random order never cascade: they
  promote only at density about `0.53 n` (`j = 1`) and `1.25 n` (`j = 2`),
  against `0.157 n` for lawful seeds. Greedy search over all types
  (`n = 1000`, 300 candidates per step) picked **0 overfold seeds** in 112
  steps and finished at `0.112 n` against `0.114 n` lawful-only.
- **New decomposition: (O-rel), a lawful-yield bound for every seed set.**

  ```text
  (O-rel)   ℓ(P) ≤ |P|  for every finite seed set P on every finite Q.
  ```

  (O-rel) implies (O). Take `P` optimal for `deep_j`, so
  `cl(P) ⊇ K`. Then `law_j = ℓ(P) ≤ |P| = deep_j`. The reverse
  inequality `deep_j ≤ law_j` is already proved. The weak form
  `ℓ(P) ≤ C |P|` gives `deep_j ≥ law_j / C`, which is the weak form that
  step 5 of the route needs.
- **(O-rel) is checkable seed set by seed set, and it can fail.** It is
  stronger than (O), since it constrains closures that do not contain `K`.
  In the relative-rank language of the target node it reads: for
  `H = ⟨K_S, g_1, …, g_k⟩` with `g_i` in the seed double cosets, the
  subgroup `H ∩ L_j` is generated over `K_S = S ∩ L_{j+1}` by at most `k`
  elements of `D_law`. This is a relative Howson/Hanna Neumann statement.
  For general pairs of free subgroups, `rk(H ∩ L)` can exceed `rk H`, so a
  proof must use the chain.
- **Computed: (O-rel) holds strictly in every tested case.**
  - 56,200 seed sets were tested, pure and mixed, at `j = 1, 2`. They were
    clustered on `n = 10^5` levels, or spread over whole small levels
    (`n = 5..20`, where closures see cycles).
  - 20,832 of them had a nontrivial lawful part.
  - In every one of those, `ℓ(P) ≤ |P| − 1`, and this value is certified,
    since it is an explicit cover.
  - So far, each overfold seed costs at least one full lawful seed of yield.
- **Inductive sub-lemma (O-step).** For every nonempty `P` there is some
  `s ∈ P` with `ℓ(P) ≤ ℓ(P − s) + 1`.
  - (O-step) implies (O-rel) by induction on `|P|`, since `ℓ(∅) = 0`.
  - In 9,600 tests at `k = 3, 4` (`j = 1, 2`), the jump
    `ℓ(P) − max_s ℓ(P − s)` was always 0 or 1.
  - This is a statement about one seed added to a closed family. It is the
    natural target for a proof.
  - Caveat: the computed `ℓ` values are upper bounds (see §3), so the jump
    statistic is heuristic. The (O-rel) checks are rigorous.

## 2. Random thresholds (`cascade.c`)

`Q` is two uniform random permutations of `{0..n−1}`. This is the random-lift
model of the witness towers. Seeds of one class are added in uniform random
order, and each run records the exact number of seeds at which `cl ⊇ K`.
Here `D0` is the initial number of kernel defects (`= 5n` at `j = 1`,
`= 12n` at `j = 2`).

| j | n | seed class | seeds in class | hit / n (2 runs) |
|---|---|---|---|---|
| 1 | 20000 | lawful | n | 0.1580, 0.1545 |
| 1 | 20000 | overfold (all level 0) | 11n | 0.5326, 0.5332 |
| 1 | 20000 | all types | 12n | 0.5072, 0.5104 |
| 2 | 5000 | lawful | n | 0.1600, 0.1544 |
| 2 | 5000 | overfold | 87n | 1.2630, 1.2656 |
| 2 | 5000 | all types | 88n | 1.2614, 1.2412 |

Greedy search at `j = 1`, `n = 1000`: at each step, the best of 300 sampled
candidates by the resulting defect count is kept.
- Over all types: 112 seeds (`0.112 n`), with **0 overfold seeds chosen**.
- Lawful only: 114 seeds (`0.114 n`).

Reading. On the random-lift towers there is no overfold cascade. In random
order, overfold seeds are 3.4 to 8 times less efficient than lawful ones.
When greedy search is offered overfold seeds, it never takes one. The
lawful density `≈ 0.157` is far above the proved floor
`(1 − λ)/6 ≥ 1/60` of
[[fpbs-mal-twisted-level-seed-density-random-lift-proof]]. This is evidence
only: random order and greedy search are not the minimum.

Files: `rand_n20000_j1_{law,lev0,over,all}.txt`,
`rand_n5000_j2_{law,over,all}.txt`, `greedy_n1000_j1_{law,all}.txt`
(`run_all.sh`).

## 3. Lawful-yield test (`oloc.py`)

Method.
1. Pick a random point `q0`. Draw `k` overfold seeds (and optionally `l`
   lawful seeds), each at a uniform point of the radius-`r` ball around
   `q0` in the Schreier graph of `Q`, with a uniform type.
2. Compute `cl(P)` with a local union-find, then its lawful part
   `N = cl(P) ∩ K`.
3. Compute `ℓ̂` = the least `s ≤ |P| + 1` such that `s` pairs taken inside
   `N` have a closure containing `N`. Candidates are deduplicated by their
   closure.
   - `ℓ̂ ≥ ℓ`, so `ℓ̂ ≤ |P|` certifies (O-rel) for that `P`.
   - `ℓ̂ = |P| + 1` would flag a candidate violation, to be re-checked with
     candidates outside `N`.
   - None was flagged.

A bug found in testing: the first closure routine dropped root vertices,
which made single-seed closures look empty. It was fixed before any run
recorded here.

| j | n | k overfold + l lawful | r | trials | nontrivial N | max ℓ̂ − \|P\| |
|---|---|---|---|---|---|---|
| 1 | 10^5 | k = 2, 3, 4; l = 0 | 0, 1, 2 | 27000 | 6028 | −1 |
| 2 | 10^5 | k = 2, 3; l = 0 | 0, 1 | 12000 | 357 | −1 |
| 1 | 10^5 | (1,1), (2,1), (3,1), (2,2) | 0, 1 | 8000 | 8000 | −1 |
| 2 | 10^5 | (1,1), (2,1) | 0, 1 | 4000 | 4000 | −1 |
| 1 | 6, 8, 12, 20 | (2,0), (3,0), (1,1), (2,1) | whole Q | 4000 | 1844 | −1 |
| 2 | 5, 8, 12 | (2,0), (1,1) | whole Q | 1200 | 603 | −1 |

Totals: 56,200 seed sets, 20,832 with nontrivial `N`, and 0 with
`ℓ̂ > |P| − 1`.

On small levels the lawful part can be large. For example, 3 overfold
seeds at `n = 8`, `j = 1` gave `rank N = 40`, and 2 lawful seeds still
cover it. So the bound is not an artefact of tiny closures.

Files: `oloc_results.txt`, `oloc_mixed_results.txt` and
`oloc_small_results.txt` (`run_oloc.sh`, `run_oloc_mixed.sh`,
`run_oloc_small.sh`). The one-step test is in `ostep.py`, with results in
`ostep_results.txt` (`run_ostep.sh`).

| j | n | k | r | trials | jump 0 | jump 1 | jump ≥ 2 |
|---|---|---|---|---|---|---|---|
| 1 | 10^5 | 3 | 0 | 3000 | 2755 | 245 | 0 |
| 1 | 10^5 | 4 | 0 | 2000 | 1784 | 216 | 0 |
| 1 | 10^5 | 4 | 1 | 2000 | 1975 | 25 | 0 |
| 1 | 12 | 4 | whole | 300 | 299 | 1 | 0 |
| 2 | 10^5 | 3 | 0 | 2000 | 1993 | 7 | 0 |
| 2 | 8 | 3 | whole | 300 | 300 | 0 | 0 |

## 4. The decomposition

### Proofs

- **(O-rel) ⇒ (O).** Let `P` attain `deep_j(Q)`, so `cl(P) ⊇ K`. Then
  `cl(P) ∩ K = K`, and by definition `ℓ(P) = law_j(Q)`. So (O-rel) gives
  `law_j ≤ deep_j`. The node
  [[fpbs-mal-depth-promotion-equals-overfold-merge-number]] proves
  `deep_j ≤ law_j`. With the constant `C` in place of 1, the same argument
  gives `deep_j ≥ law_j / C`. That is exactly the input step 5 of
  [[fpbs-mal-depth-floor-from-overfold-domination]] needs, together with
  the proved `law_j ≥ n/60` on random lifts.
- **(O-step) ⇒ (O-rel).** Induct on `|P|`, starting from `ℓ(∅) = 0`. Every
  proper subset satisfies the bound by induction, so
  `ℓ(P) ≤ ℓ(P − s) + 1 ≤ (|P| − 1) + 1`.
- **Single overfold seed on a tree-like level (proved).** Suppose the
  radius of the level exceeds the seed-type tree. Then `ℓ({o}) = 0`.
  - The closure of one seed is its pair tree, translated to `q`, with no
    transitivity. Its pairs are `(q·w; c·w, c'·w)`, and on a tree-like
    region no two of them share a vertex off the diagonal.
  - By Lemma A of the census entry, fold consequences of an overfold pair
    are overfold. So the closure has no lawful pair.
  - This is the base case of the strict pattern `ℓ ≤ |P| − 1` that was
    observed.

### Relation to (F) and (O') of the free-fold entry

- Conjecture (F) of
  `research/artifacts/fpbs-overfold-free-fold-2026-09-19.md` is (O-rel)
  restricted to *realizable hits*: `J ∩ L_{j+1} = K` and
  `[L_j : J ∩ L_j] = d`. That entry shows (O) ⇒ (F).
- (O-rel) asks the same bound for *every* seed set, including closures that
  are not hits. Exactly this extension is what makes induction possible.
  Building `P` one seed at a time necessarily passes through non-hit
  intermediate families, so (F) cannot be proved by induction on `k`,
  while (O-rel) can, via (O-step).
- (O') is `law(K') ≤ δ(J)`, a rank-drop bound at hits. It is a different
  quantity.

### What (O-rel) says in group terms

Take `Q` transitive, with `S`, `K_S = S ∩ L_{j+1}`, `K' = S ∩ L_j` and
`D_law`, `D_i` as in the node's relative-rank form. For seeds with loops
`g_1, …, g_k`, put `H = ⟨K_S, g_1, …, g_k⟩`. Then `cl(P) ∩ K` corresponds
to `H ∩ L_j`, and

```text
(O-rel)  H ∩ L_j ≤ ⟨K_S, h_1, …, h_k⟩  for some h_i ∈ K' ∩ D_law.
```

The correspondence follows the node's proof of the relative-rank form. Two
vertices reached by `w` and `w'` are identified by `cl(P)` iff
`w w'^{-1} ∈ H`, and they lie in one `m`-fibre iff `w w'^{-1} ∈ K'`.

This is a *relative Howson inequality*: intersecting with `L_j` never needs
more new generators over `K_S` than `H` has.
- Since `rk L_j = 2`, SHNC (Friedman, Mineyev) gives only the absolute
  bound `rk(H ∩ L_j) ≤ rk H`.
- That does not imply generation *over* `K_S` by elements of `D_law`: `K_S`
  need not be a free factor of `H ∩ L_j`. The node records SHNC counting
  as a dead route for this reason.
- So a proof has to use more of the chain: malnormality (seed types are
  trees) and the single lawful component.

The computations say the chain does satisfy it, strictly, whenever an
overfold element is used.

### What would kill it, and why it matters

- A single seed set with `ℓ(P) > |P|`, on any finite `Q`, refutes (O-rel)
  and (O-step). It does not refute (O).
- A seed set with `ℓ(P) > C|P|` for every `C`, on the random-lift towers,
  would show that the weak form of (O) cannot be proved seed by seed. Any
  proof would then have to be global, for example by percolation.
- Conversely, (O-step) is a statement about adding one seed to one closed
  family. That is where a proof should aim: exhibit, for the new seed `s`,
  one lawful seed that recovers the new lawful identifications modulo the
  old lawful closure.
  - The failures of the naive one-for-one exchange recorded in the node
    (12 of 135 single swaps at `j = 2`) concern replacing a seed while
    keeping `cl ⊇ K`. That is a different, stronger requirement, and it
    does not contradict (O-step).
