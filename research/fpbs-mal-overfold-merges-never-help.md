---
rg: 2
id: fpbs-mal-overfold-merges-never-help
kind: claim
title: On every finite F(a,b)-set, merges of the folded L_{j+1}-graph outside the kernel of its map onto the folded L_j-graph never lower the least number of merges that collapse that kernel, so deep_j(Q) = law_j(Q) = r(Q^(j))
distinct_from:
  fpbs-mal-depth-promotion-equals-overfold-merge-number: that proves Q_j(X) = inf_m deep_j(Q_m)/|Q_m| and deep_j <= law_j = r(Q^(j)); this is the open reverse inequality deep_j >= law_j, which that node does not decide.
  fpbs-word-chords-are-dominated-by-merges: that shows arcs with arbitrary labels are dominated by vertex merges of one folded graph; this asks that merges which are not in the kernel be dominated by merges that are, a different exchange.
  fpbs-mal-bernoulli-single-stage-floor: that is the Bernoulli floor; this is one of the two finite inputs of the route fpbs-mal-depth-floor-from-overfold-domination to it.
  fpbs-mal-twisted-level-seed-density-uniform-witness: that is the other input, a uniform lower bound on r(Q_m^(j))/|Q_m|; this is the exchange statement that turns lawful seeds into all seeds.
artifacts:
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_search.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n4_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n5_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n6_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n8_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n4_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_n5_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/seedtypes.py
  - experiments/fpbs-depth-overfolding-2026-09-17/pair_automaton.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange_n40_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange_sanov29_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/exchange_n20_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/compare.py
  - experiments/fpbs-depth-overfolding-2026-09-17/compare_n30_j1.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/compare_n20_j2.txt
  - experiments/fpbs-depth-overfolding-2026-09-17/compare_n12_j3.txt
  - research/artifacts/fpbs-overfold-intransitive-levels-2026-09-19.md
  - experiments/fpbs-overfold-sharing-2026-09-17/intransitive_exact.py
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n5_j1.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n8_j1.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n6_j1_3orb.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n4_j2.txt
  - experiments/fpbs-overfold-sharing-2026-09-17/run_n5_j2.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exhaustive.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exh_n6_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exh_n5_j2.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/pairtrees.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/multiorbit.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exact_multi.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/localsearch.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/local_cayley24_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/top_vs_law.py
  - experiments/fpbs-overfold-relative-rank-2026-09-17/top_vs_law_n6_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exact_multi_s3_j1.txt
  - experiments/fpbs-overfold-relative-rank-2026-09-17/exh_n3_j3.txt
---

**OPEN.** Notation is as in
[[fpbs-mal-depth-promotion-equals-overfold-merge-number]]. Here `Q` is a
finite `L`-set, `m : Γ_{j+1}(Q) → Γ_j(Q)` is the canonical surjection, and:
- `deep_j(Q)` is the least number of same-fibre pairs of `Γ_{j+1}(Q)` whose
  fold-closure contains `ker(m)`;
- `law_j(Q)` is the same least number, over pairs inside `ker(m)`.

Prove that for every finite `Q` and every `j ≥ 0`,

```text
deep_j(Q)  =  law_j(Q)   ( = r(Q^{(j)}) ).
```

A weaker statement suffices for the floor: `deep_j(Q) ≥ c · law_j(Q)`, with
`c > 0` independent of `j` and `Q`.

**Why it matters.**
- With [[fpbs-mal-depth-promotion-equals-overfold-merge-number]], this gives
  `Q_j(X) = Q_j^law(X)` on every essentially free profinite `X`. That is:
  - labels outside `L_j` never help promote `E_{L_{j+1}}` to `E_{L_j}`;
  - the promotion problem at depth `j` is the depth-0 problem of the
    twisted levels `Q_m^{(j)}`.
- This is statement (U) of the w14 D1 setup, on profinite witnesses, with
  `c = 1`.

**Known.**
- `j = 0`: `Γ_0(Q)` is the Schreier graph, so every same-fibre pair lies in
  `ker(m)`. Equality is trivial.
- `deep_j ≤ law_j` always.

**Evidence (computations).**
- **Exact values.** `exact_search.py` computes both numbers exactly by
  breadth-first search over the distinct partitions reached by `k` seeds.
  - It covers 70 random transitive levels: `j = 1` with `n = 4, 5, 6, 8`,
    and `j = 2` with `n = 4, 5`.
  - The graphs `Γ_{j+1}(Q)` have up to 100 vertices.
  - In all 70 cases, `deep_j = law_j`.
  - The files `exact_n5_j1.txt`, `exact_n8_j1.txt` and `exact_n5_j2.txt`
    were made before a fix to partition deduplication. The fix only speeds
    the search up, and the values found are still exact.
- **Exchange.** `exchange.py` takes random inclusion-minimal promoting seed
  sets of mixed types. It tries to swap each overfold seed for a single
  lawful seed.
  - At `j = 1`: 0 failures among 208 overfold seeds on random `n = 40`
    levels, and 0 among 80 on the Sanov line `P^1(F_29)`.
  - At `j = 2`: 12 of 135 single swaps fail. These are on non-minimum sets,
    so a proof cannot be a naive one-for-one local exchange.
  - No short word `w` gives a uniform exchange rule `y ↦ y·w` per seed type.
- **Heuristic search.** `compare.py` runs greedy search with restarts over
  all seed types. It never found fewer seeds than the exact `law_j`:
  - `j = 1`, `n = 30`: 8 levels;
  - `j = 2`, `n = 20`: 8 levels;
  - `j = 3`, `n = 12`: 5 levels.
- **Structure.** Over the finite core of `L_{j+1}` (one point), the lawful
  pairs form a single component of the pair graph. The overfold pairs form
  11, 87 and 559 components for `j = 1, 2, 3` (`seedtypes.py`,
  `pair_automaton.py`). So overfold seed types multiply quickly, but no
  computed instance uses one profitably.

**What a proof must use.** For a general pair of subgroups in place of
`L_{j+1} ≤ L_j`, the analogous exchange has no reason to hold. Its
generating-set analogue fails: a subgroup of a 2-generated finite group can
need 3 generators. So a proof has to use features special to this chain,
such as rank 2 and the single lawful component above.

## Attempts

- **Cross-orbit sharing on `L_j`-intransitive levels** (swarm-0917-w16-w16-fp-break,
  belief breaker, 2026-09-19). No counterexample found.
  - *Idea.* `law_j` is additive over `L_j`-orbits. A single overfold pair
    whose ends map to different `L_j`-orbits could serve two orbit kernels,
    giving `deep < law`. The earlier 70 levels were almost all
    `L_j`-transitive, so they never tested this.
  - *Computation.* `intransitive_exact.py` computes `law_j` and `deep_j`
    exactly on 53 `L`-transitive levels with at least 2 `L_j`-orbits:
    - `j = 1`: `n = 5`, `n = 8`, and `n = 6` with 3 orbits;
    - `j = 2`: `n = 4, 5`.
  - *Result.* `deep_j = law_j` in all 53. In 17 of them the minimum witness
    contains overfold seeds, but never with fewer seeds. The script counts
    overfold seeds; it does not separate the cross-orbit ones.
  - *Proved on the way (Lemma A of the artifact).* Every promoting seed set
    has at least `sum_O (s_O - 1)` seeds, where `s_O` is the number of
    `L_{j+1}`-orbits in the `L_j`-orbit `O`. This holds with or without
    cross-orbit seeds.
    - So cross-orbit seeds cannot save on connectivity. Any sharing would
      have to come from fold-closure identifications.
    - The bound has density 0 on free towers, so it is not a floor.
  - *Where it dies.* The sharing mechanism is never observed. The open case
    is still large transitive levels, beyond exact search.
  - Details: `research/artifacts/fpbs-overfold-intransitive-levels-2026-09-19.md`.
- **2026-09-19, swarm-0917-w16-w16-fp-last1 (census-computation +
  reframing): OPEN; no counterexample; exact reformulation.** Scripts and
  outputs are in `experiments/fpbs-overfold-relative-rank-2026-09-17/`.
  - **Pullback form (proved here).** Let `R` be the rose on `a, b`, `C_j`
    the Stallings core of `L_j`, and `ι : C_{j+1} → C_j` the immersion
    induced by `L_{j+1} ≤ L_j`. Then:
    - `Γ_{j+1}(Q) = Q ×_R C_{j+1}`, with `m = id × ι` and the over map
      equal to the first projection.
    - Proof: the fold of the generator paths maps onto this pullback, which
      is folded. The map is injective: if `p·u = p'·u'` and `u, u'` end at
      the same core vertex, then `r = u u'^{-1} ∈ L_{j+1}` is readable from
      `p` and ends at `p'`. So `r u'` is readable from `p`, and it reduces to
      `u`. By determinism, both endpoints coincide.
    - So a same-fibre pair is `(q; c, c')` with `c, c' ∈ V(C_{j+1})`, and it
      is lawful iff `ι c = ι c'`.
    - A fold closure is the least family `(E_q)_{q∈Q}` of equivalence
      relations on `V(C_{j+1})` that contains the seeds and satisfies:
      `c E_q c'` and `x` readable at both imply `cx E_{qx} c'x`.
  - **Seed types are finite trees.** A seed type is an off-diagonal
    component of the pair graph `C_{j+1} ×_R C_{j+1}`.
    - The type of `(c, c')` corresponds to the double coset
      `L_{j+1} u_c u_{c'}^{-1} L_{j+1}`. Its `π_1` is
      `L_{j+1} ∩ g L_{j+1} g^{-1}`, which is trivial by malnormality.
    - `pairtrees.py` checks that every component is a tree, for
      `j = 0..3`. The counts of ordered components are 2, 24, 176 and 1120.
      Of these, exactly 2 are lawful, which is one unordered type. The
      remaining 11, 87 and 559 unordered types are overfold.
    - Consequence: one seed yields a fixed finite set of `|T_i|`
      identifications, whatever `Q` is. Every dependence of the closure on
      `Q` comes from transitivity inside fibres.
  - **Relative-rank form (proved here, `Q` transitive under `L_{j+1}`).**
    Fix a base point `p` and set:
    - `S = Stab_L(p)`, `K = S ∩ L_{j+1}` and `K' = S ∩ L_j`;
    - `D_law` for the lawful double coset of `L_{j+1}` (it lies in `L_j`);
    - `D_1, …, D_r` for the overfold double cosets (they lie in
      `L ∖ L_j`).

    A seed at the vertices reached by words `u` and `u'` contributes the
    loop `g = u u'^{-1}` to `π_1`. Then:
    - the seed is same-fibre iff `g ∈ S`, and lawful iff `g ∈ K'`;
    - every `g ∈ S ∩ D_i` is realised by some seed;
    - the closure contains `ker(m)` iff `⟨K, g_1, …, g_k⟩ ⊇ K'`. This holds
      because vertices reached by `w` and `w'` coincide in a folded graph
      iff `w w'^{-1} ∈ π_1`.

    Hence:

    ```text
    deep_j(Q) = min{ k : g_i ∈ S ∩ (D_law ∪ D_1 ∪ … ∪ D_r), ⟨K, g⟩ ⊇ K' }
    law_j(Q)  = min{ k : g_i ∈ K' ∩ D_law,                   ⟨K, g⟩ = K'  }
    ```

    Any witness `H = ⟨K, g⟩` satisfies `H ∩ L_j = K'` and
    `H ∩ L_{j+1} = K`. So (O) says exactly this: elements of the overfold
    double cosets, which lie outside `L_j`, never generate `K'` over `K`
    more cheaply than elements of `D_law`. This is a relative-rank statement
    for the malnormal chain `L_{j+1} < L_j < L`.
  - **Exhaustive census.** `exhaustive.py` covers every transitive `L`-set
    of size `n`, up to isomorphism (7, 26, 97 and 624 classes for
    `n = 3, 4, 5, 6`, the counts in OEIS A057005).
    - `law_j` is computed exactly, as a sum over the components of
      `Γ_j(Q)`.
    - `deep_j < law_j` is then ruled out by exact breadth-first search over
      all same-fibre seeds, up to level `law_j − 1`.
    - Results: `deep_j = law_j` in every class, with no flags:
      - `j = 1`, `n ≤ 6`: law values 1–4; 624 classes at `n = 6`, 92 of
        them not `L_1`-transitive;
      - `j = 2`, `n ≤ 5`: 24 of 97 classes at `n = 5` are not
        `L_2`-transitive;
      - `j = 3`, `n = 3`.
    - Classes that are not `L_j`-transitive are new ground. Only there can a
      seed join two components of `Γ_j(Q)` (a cross-orbit seed), and the
      random census never produced such a `Q`.
  - **Structured levels (heuristic).** These are the Cayley actions of every
    2-generated subgroup of `S_3`, `S_4` and `S_5` of order at most 24.
    - `localsearch.py` does 10 restarts of 300 swap steps each, over all
      seed types, with `k = law − 1` seeds.
    - It found no witness to `deep < law` on 54 levels at `j = 1`
      (`local_cayley24_j1.txt`).
    - These levels include law values up to 12, and levels with up to 6
      `L_1`-orbits, where cross-orbit seeds are plentiful.
    - The exact search `exact_multi.py` gives these values
      (`exact_multi_s3_j1.txt`):
      - `S_3` with 3 orbits: `law = 3` and `deep = 3`;
      - an order-12 group with 3 orbits: `law = 6` and `deep ≥ 4`.
  - **Top family is not a shortcut.** Let `full_j` be the least number of
    seeds that collapses every fibre onto `Q`, so that `deep_j ≤ full_j`.
    - On 15 random levels with `n = 6` and `j = 1`, `full_1 > law_1` holds
      exactly in 14 of them (`top_vs_law_n6_j1.txt`). The 15th has
      `law_1 = 3` and `full_1 ≥ 3`.
    - So a counterexample, if one exists, sits at an intermediate closed
      family.
  - **Cheap bound (proved).** Let `N` be the number of components of
    `Γ_j(Q)` with nontrivial kernel. Folding never leaves a connected
    component, and one seed touches at most two components. Hence
    `deep_j(Q) ≥ ⌈N/2⌉`, whereas `law_j(Q) ≥ N`.
  - **Remaining gap.** Two things are still missing:
    - a proof of the relative-rank statement above, or its weak form with a
      constant `c`;
    - evidence at larger `n`, where 2-of-3 percolation can chain overfold
      pairs over long distances.

    Homological certificates do not transfer to `deep`, for two reasons:
    - `L_j` is not a free factor. Its abelian image is all of `Z^2`, so no
      nontrivial character kills it.
    - `H_1(K') → H_1(H)` need not be injective.

    For the same reason, the 1-dimensional local-system bound on `law` does
    not bound `deep`.
