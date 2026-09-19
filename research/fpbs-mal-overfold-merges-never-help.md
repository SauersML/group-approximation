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
