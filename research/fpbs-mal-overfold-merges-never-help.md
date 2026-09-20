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
  - research/artifacts/fpbs-overfold-free-fold-2026-09-19.md
  - experiments/fpbs-overfold-free-fold-2026-09-17/freefold.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/bfs_free.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/check_law0.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/law_census.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/census_d6.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/all_single.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/as_j1_d5.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/as_j1_d6.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/as_j2_d4.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/single_stats.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/stats_j1_d5.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/stats_j2_d4.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/stats_j3_d2.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/level2.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/l2_j1_d4.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/l2_j1_d6.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/retract_test.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/rt_j1_d3.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/rt_j2_d2.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/check_nonsplit.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/check_nonsplit.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/rank_states.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/rank_states_j1_d3.txt
  - experiments/fpbs-overfold-free-fold-2026-09-17/matching.py
  - experiments/fpbs-overfold-free-fold-2026-09-17/matching_j1_d4.txt
  - research/artifacts/fpbs-overfold-exact-c-census-2026-09-19.md
  - experiments/fpbs-overfold-exact-c-2026-09-17/deep.c
  - experiments/fpbs-overfold-exact-c-2026-09-17/export.py
  - experiments/fpbs-overfold-exact-c-2026-09-17/check_auts.py
  - experiments/fpbs-overfold-exact-c-2026-09-17/census.py
  - experiments/fpbs-overfold-exact-c-2026-09-17/run12_j1_cap5.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/run24a_cap4.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/run24b_cap4.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/census_cayley24_j1_cap3.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/census_cayley24_j1_law5_cap4.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/census_cayley24_j2_cap3.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/run20e_cap4.txt
  - research/artifacts/fpbs-overfold-depth-shift-reduction-2026-09-19.md
  - experiments/fpbs-overfold-breaker-2026-09-17/pb.py
  - experiments/fpbs-overfold-breaker-2026-09-17/smallk.py
  - experiments/fpbs-overfold-breaker-2026-09-17/reduction_check.py
  - experiments/fpbs-overfold-breaker-2026-09-17/principal_types.py
  - experiments/fpbs-overfold-breaker-2026-09-17/principal_types_j4.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/doublecoset_check.py
  - experiments/fpbs-overfold-breaker-2026-09-17/doublecoset_j4.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j1_n7.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j2_n6.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j3_n4.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/exh_j4_n3.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j1_n14.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j2_n9.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j3_n8_single.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/rand_j4_n5_single.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/redcheck_j2_i1_n5.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/redcheck_j3_i1_n3.txt
  - experiments/fpbs-overfold-breaker-2026-09-17/redcheck_j3_i2_n3.txt
  - research/artifacts/fpbs-overfold-cascade-2026-09-19.md
  - experiments/fpbs-overfold-cascade-2026-09-17/export_model.py
  - experiments/fpbs-overfold-cascade-2026-09-17/model_j1.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/model_j2.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/cascade.c
  - experiments/fpbs-overfold-cascade-2026-09-17/run_all.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_law.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_over.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_all.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n5000_j2_law.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n5000_j2_over.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n5000_j2_all.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/greedy_n1000_j1_all.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/greedy_n1000_j1_law.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc.py
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc_mixed_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/oloc_small_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/ostep.py
  - experiments/fpbs-overfold-cascade-2026-09-17/ostep_results.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/rand_n20000_j1_lev0.txt
  - experiments/fpbs-overfold-cascade-2026-09-17/run_oloc.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/run_oloc_mixed.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/run_oloc_small.sh
  - experiments/fpbs-overfold-cascade-2026-09-17/run_ostep.sh
  - research/artifacts/fpbs-overfold-one-pair-joins-2026-09-19.md
  - experiments/fpbs-overfold-one-pair-2026-09-17/folding.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/test_lemma1.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/test_lemma1.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/expansion.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/expansion_check.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/monphi_k1.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/run_s2_g5_l8.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/run_s3_g3_l10.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/run_s4_g6_l5.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/witness.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/witness_W.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/ri_k1.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/ri_j1_s11.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/ri_j2_s13.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/selftest_ri.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/selftest_ri.txt
  - experiments/fpbs-overfold-one-pair-2026-09-17/transfer.py
  - experiments/fpbs-overfold-one-pair-2026-09-17/transfer2.py
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
- **2026-09-19, swarm-0917-w17-w17-fp-pull (reframer + compute scout):
  OPEN; one lemma proved, one route killed, exact checks made
  `Q`-universal.** Details are in
  `research/artifacts/fpbs-overfold-free-fold-2026-09-19.md`, with scripts
  in `experiments/fpbs-overfold-free-fold-2026-09-17/`.
  - **Free-fold form (proved, Proposition 1).** Let `K` have index `d` in
    `L_{j+1}`. A seed is a vertex pair of `Γ_K`, and `J = ⟨K, g_1..g_k⟩`
    is the result of `k` seed folds. Call `J` realizable if
    `J ∩ L_{j+1} = K`, and a hit if `[L_j : J ∩ L_j] = d`.
    - (F) says: every realizable hit has `rk(J ∩ L_j : K) ≤ k`.
    - (O) implies (F), using M. Hall's theorem to build a finite-index
      `S ⊇ J` with `S ∩ L_j = J ∩ L_j`.
    - (F) implies (O) on every `L_j`-orbit that is a single
      `L_{j+1}`-orbit, in every finite `Q`.
    - So exact checks of (F) at fixed `d` hold for all `Q`, of any size.
      They do not reach cross-orbit levels.
  - **Exact verification.** Two scripts do the checks:
    - an all-class single-seed scan, `all_single.py`: 0 realizable
      overfold hits for `d ≥ 2`;
    - an exact two-seed BFS on the three law-3 classes at `d = 6`,
      `level2.py`: no law-3 `K'` is reached.

    Together they give (O) on coincident orbits of size `d ≤ 6` for
    `j = 1`, and `d ≤ 4` for `j = 2`, in every finite `L`-set.
  - **No-drop lemma (proved, Lemma 2).** Every hit has
    `δ = rk K + k − rk J ≥ 1`.
    - Suppose `δ = 0`. Hopficity gives `J = K * ⟨g⟩` and
      `J = K' * ⟨g⟩`, because `rk K = rk K' = d + 1`.
    - Killing the `g_i` then maps both `K` and `K'` isomorphically onto
      the same quotient, so `K = K'`.
    - That is impossible, since `[L_j : L_{j+1}] = ∞`.
  - **Conjecture (R)** is the missing input for the level-1 case of (O),
    which is `deep = 1 ⇒ law = 1`, for all `j` and `d`.
    - (R) says a realizable single overfold seed with `d ≥ 2` never drops
      rank. Lemma 2 then does the rest.
    - It is checked for `j = 1, d ≤ 5`; `j = 2, d ≤ 4`; `j = 3, d ≤ 2`.
    - It is false at `d = 1`, where it is harmless.
    - Two proof routes fail on the data: the closure is not a matching of
      the tree type, and SHNC equality does not force finite index.
  - **Conjecture (O')** is `law(K') ≤ δ(J)`. It implies (F). There are 0
    violations in the depth-2 runs.
  - **Where it dies: the retract route (G) is false.** (G) says `K'` is a
    retract of every witness `J`, or a free factor, or split in `H_1`.
    - The first law-2 level already refutes it: `j = 1`, `Q = Z/3` with
      `a = +1` and `b = −1`, so `law = 2`.
    - Two seeds give `J = S`. The map `H_1(K') → H_1(S)` has determinant
      −4, computed independently by Reidemeister–Schreier in
      `check_nonsplit.py`.
    - So no proof of (O) can go through a map `J → K'` that fixes `K'`.

- **2026-09-19, swarm-0917-w17-w17-fp-last1 (census-computation).** Exact C
  solver on the hardest known levels. No counterexample; the target stays
  OPEN. Details are in
  `research/artifacts/fpbs-overfold-exact-c-census-2026-09-19.md`.
  - *Tools.* `export.py` writes instances, and `deep.c` searches them.
    - The search is an exact breadth-first search over fold-closed
      partitions, reduced by the lifted automorphisms of `Q`.
    - `check_auts.py` verifies that those automorphisms are valid.
    - The lawful-only mode reproduces every known `law` value.
  - *Order-12 three-orbit Cayley level*, `(0,1,2,4,3),(1,0,3,4,2)` at
    `j = 1` (`run12_j1_cap5.txt`):
    - `law = 6`, and all-seed search is exhaustive up to 5 seeds, covering
      793171 states and 114216624 extensions;
    - so `deep = 6 = law`. w16 had only reached `deep ≥ 4`.
  - *The two `n = 24` three-orbit levels with `law = 6`*,
    `(0,1,3,2),(1,2,0,3)` and `(1,2,3,0),(0,2,3,1)`: `deep ≥ 5` for both
    (`run24a_cap4.txt`, `run24b_cap4.txt`).
  - *Census over the 54 Cayley levels of `local_cayley24_j1.txt`*
    (`census.py`):
    - at `j = 1`, `deep = law` exactly on every level with `law ≤ 5`;
    - every level with `law ≥ 6` has `deep ≥ 4`, and the three `law = 6`
      levels have `deep ≥ 5`;
    - at `j = 2` (`V ≤ 256`), `deep = law` wherever `law ≤ 4`.
  - *Lemma A (proved).* Fold consequences of a lawful pair are lawful, and
    those of an overfold pair are overfold, because `Γ_j(Q)` is folded.
    - Lawful identifications from overfold seeds therefore arise only by
      transitivity, along cycles of overfold orbits through `Γ_j(Q)`.
  - *Hanna Neumann counting is vacuous (proved).*
    - The strengthened Hanna Neumann inequality for `H = ⟨K, seeds⟩` and the
      rank-2 group `L_j` gives only `deep ≥ |p·L_j| − |p·L_{j+1}|`, summed
      over components. That is the orbit-count bound.
    - The other double-coset terms are unforced, since `L_j` is malnormal.
    - So on towers with `o(|Q|)` orbits of `L_{j+1}`, this route cannot give
      the floor.
  - *Remaining.* The weak form `deep ≥ c · law` has to use the double-coset
    restriction on seeds, or the cycle structure from Lemma A.
- **2026-09-19, swarm-0917-w17-w17-fp-break (belief breaker): OPEN; no
  counterexample; (O) reduced to its level-0 part.** Details:
  `research/artifacts/fpbs-overfold-depth-shift-reduction-2026-09-19.md`.
  Scripts: `experiments/fpbs-overfold-breaker-2026-09-17/`.
  - **Levels.** The level of a seed type at depth `j` is the largest `i`
    with equal images in `C_i`. Equivalently, `g = u_c u_{c'}^{-1} ∈ L_i`.
    - Level `j` is the lawful type.
    - At depth `j` there are `N_{j-i}` types of level `i`, with
      `N = 1, 11, 76, 472, 2821` (`j ≤ 4`).
    - Level-0 types have tree size `≤ 3`.
  - **Lemma D (depth shift).** Let `deep_j^{≥i}` allow only seeds of level
    `≥ i`. Then

    ```text
    deep_j^{≥i}(Q) = deep_{j-i}(Q^{(i)})   and   law_j(Q) = law_{j-i}(Q^{(i)}).
    ```

    - *Proof.* From the relative-rank form above: level `≥ 1` means
      `g ∈ L_1`, and `φ` transports `(S ∩ L_1, K, K')` to the depth-`(j−1)`
      data of `Q^{(1)}`. The one extra input is the double-coset identity
      (T_j): `U_j ∩ L_1 = φ(U_{j-1})`, where `U_j` is the union of the
      realised double cosets of `L_{j+1}`.
    - (T_j) is basis-dependent: minimal subtrees in `T(L; a, b)` versus
      `T(L_1; a, t_1)`. It is checked exactly for `j ≤ 4` by a
      tree-projection test (`doublecoset_check.py`).
    - Scope: `L_{j+1}`-transitive `Q`.
    - Independent check: `reduction_check.py` gives matching closure and
      promotion fingerprints on 22 random `Q`.
    - Dead end, recorded: the naive proof via principal pairs fails, since
      1, 9 and 64 level-≥1 types contain no principal pair
      (`principal_types.py`).
  - **Corollary.** (O) is equivalent to (O'_j): `deep_j(Q) = deep_j^{≥1}(Q)`
    at every depth. That is, only the level-0 overfold types need to be
    ruled out; all deeper types follow by induction. This is proved for
    `j ≤ 4`, and for all `j` given (T).
    - Caveat: the weak form `deep ≥ c·law` does not follow from a weak
      level-0 bound, which only compounds to `c^j`.
  - **Measure form (proved, all `j`).** `Q_j(X) ≤ Q_{j-1}(X^{(1)})` and
    `Q_j^law(X) = Q_{j-1}^law(X^{(1)})`, because graphings inside
    `E_{X|L_1}` are exactly the level-≥1 seeds.
    - For Bernoulli `ρ`, `ρ^{(1)} ≅ ρ`, so `Q_0(ρ) ≥ Q_1(ρ) ≥ …` is
      non-increasing, and `Q_j^law(ρ) = Q_0(ρ)`.
    - (O) at `ρ` says this sequence is constant. The floor says its limit
      is positive.
  - **Census, 0 FLAGs.** The pullback-model seed reducer `smallk.py`
    (validated against `exh_n5_j2`) ran on:
    - every transitive `Q` with `(j, n) = (1, 7)`: 4163 classes;
    - every transitive `Q` with `(j, n) = (2, 6)`: 624 classes;
    - every transitive `Q` with `(j, n) = (3, 4)` and `(4, 3)`;
    - random samples: `j=1, n=14` (300 levels) and `j=2, n=9` (100 levels),
      with pairs;
    - random samples, single seeds only: `j=3, n=8` and `j=4, n=5`.

    Throughout, `deep = law` whenever `law ≤ 2`.
  - **Where it dies.** No sharing mechanism is observed. A minimal
    counterexample must use a level-0 seed in every minimal witness, so a
    future hunt can be restricted to those.
- **2026-09-19, swarm-0917-w17-w17-fp-follow (compute scout,
  probability-random): OPEN; large-n evidence on the witness towers; new
  inductive decomposition (O-rel)/(O-step).** Details are in
  `research/artifacts/fpbs-overfold-cascade-2026-09-19.md`, with scripts in
  `experiments/fpbs-overfold-cascade-2026-09-17/`.
  - **No overfold cascade on random lifts.**
    - Random-order promotion on 2-permutation levels:
      - `j = 1`, `n = 20000`: lawful seeds `0.157 n`, overfold `0.533 n`,
        all types `0.51 n`;
      - `j = 2`, `n = 5000`: lawful `0.157 n`, overfold `1.26 n`.
    - Greedy search over all types (`j = 1`, `n = 1000`, 300 candidates per
      step) chose 0 overfold seeds, finishing at `0.112 n` against
      `0.114 n` lawful-only.
    - This is evidence only; random order and greedy are not the minimum.
  - **Decomposition.** Let `ℓ(P)` be the least number of lawful seeds whose
    closure contains `cl(P) ∩ ker m`.
    - (O-rel): `ℓ(P) ≤ |P|` for every finite seed set `P`.
    - (O-step): every nonempty `P` has some `s` with
      `ℓ(P) ≤ ℓ(P − s) + 1`.
    - (O-step) ⇒ (O-rel) ⇒ (O). The weak forms with a constant `C` give
      `deep ≥ law / C`, which is what step 5 of the route needs.
    - (O-rel) is (F) of the free-fold entry, extended from realizable hits
      to all seed sets. That extension is what lets induction on `|P|`
      pass through non-hit intermediate families.
  - **Checks (0 violations).**
    - 56,200 clustered or whole-level seed sets, pure and mixed, `j = 1, 2`;
      20,832 of them have a nontrivial lawful part.
    - All of these satisfy the certified bound `ℓ ≤ |P| − 1`. Strictness
      is proved for one overfold seed on tree-like levels, via Lemma A.
    - 9,600 one-step tests: the jump `ℓ(P) − max_s ℓ(P − s)` is always 0
      or 1. These values are upper bounds, so this part is heuristic.
  - **Where it stands.** No proof of (O-step). A single `P` with
    `ℓ(P) > |P|` on any finite `Q` would kill this decomposition, though
    not (O) itself.
- **2026-09-20, swarm-0917-w20-w20-fp-last1 (logic-computability): OPEN;
  the k = 1 layer of the chain (RI_{L_j}) ⇒ (G_j) ⇒ (O) is now finite and
  exact, and (W) is refuted.** Full write-up:
  `research/artifacts/fpbs-overfold-one-pair-joins-2026-09-19.md`.
  - **Lemma 1 (one-pair lemma), proved.** For f.g. `X` and any `g`, the
    join `<X, g>` falls in one of two cases.
    - Arc case: `Γ_X` embeds in `Γ_{<X,g>}` and the rank goes up by one.
    - One-pair case: `Γ_{<X,g>} = fold(Γ_X / (u ~ w))` for two vertices
      `u, w`.

    Validated by direct folding: 1846 one-pair and 1110 arc cases,
    0 mismatches.
  - **Arcs are harmless.** For every rank-2 host `B`, malnormal or not, an
    arc join satisfies `rk(J ∩ B : X) ≤ 1`. The proof uses SHN
    (`rk Y ≤ rk X + 1`) and Kurosh (`X` is a free factor of `Y`).
  - **Exact decidability.** (RI_B) at `k = 1`, E(2), (Mon_φ) at `k = 1`
    and (W) each reduce to at most `C(|V|, 2)` folds, with no bound on
    `|g|`. This supersedes the `|g| ≤ 7` searches of w18 and w19.
  - **Lemma 2 (φ-expansion dictionary).** It gives `Γ_{φ X_0}` in closed
    form, verified on 3000 random cases.
  - **Type lemma.** Same-type pairs of the expansion give joins inside
    `L_1`. Only the three mixed double cosets can reach `F`.
  - **(W) of w19-follow is REFUTED.** Take `X_0 = <aBAB, ABaba>`. Then
    `g = AbbbaBBa` (`|g| = 8`) gives `<φX_0, g> = F`, while
    `<X_0, a> ≠ F` and `<X_0, b> ≠ F`. The exact censuses found 302
    violations in total. Proof routes through "`a` or `t` completes" are
    dead.
  - **Exact censuses, all `g` at once (0 violations).**
    - (Mon_φ) at `k = 1`: 0 violations in 35498 E(2)-hits.
    - (RI_{L_1}) at `k = 1`: 0 violations in 146567 one-pair joins,
      including 18,909 with `Y ≠ X`.
    - (RI_{L_2}) at `k = 1`: 0 violations in 18313 joins, including 491
      with `Y ≠ X`.
    - Self-test: the same code finds 72 violating one-pair folds for
      w19-last1's non-malnormal host and 0 for `L_1`.
  - **Gap.**
    - `k ≥ 2`: arc-then-fold joins form an infinite family.
    - A proof of (Mon_φ) at `k = 1`, as a transfer for mixed collapsing
      pairs. Simple projection works in only 142 of 283 hits.
