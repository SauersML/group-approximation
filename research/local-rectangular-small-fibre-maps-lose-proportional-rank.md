---
rg: 2
id: local-rectangular-small-fibre-maps-lose-proportional-rank
kind: claim
title: A local map between finite products of tori whose inputs are each controlled by a bounded set of outputs loses first-cohomology rank at most proportionally to its surplus of output sites
distinct_from:
  lef-groups-are-torus-surjunctive: that contains the square, defect-free case (Theorem 1, the dimension-free small-fibre lemma), where full rank holds without locality; this is the rectangular case with a proportional surplus of outputs, where locality is necessary.
  sofic-torus-c2-reduces-to-rectangular-small-fibres: that proves this lemma implies C2 and torus surjunctivity for every sofic group; this is the lemma itself, stated without any group.
  injective-torus-automata-have-regular-degree: that is C2 for every group; this is a finite-dimensional topological statement that implies C2 for sofic groups only.
artifacts:
  - research/artifacts/sofic-torus-rectangular-small-fibre-2026-09-19.md
  - research/artifacts/zero-row-slice-count-2026-09-20.md
---

**OPEN.**

Let `d, K >= 1` and `eta > 0`. Let `g: (T^d)^I -> (T^d)^J` be continuous, with `I`, `J`
finite, and satisfy two conditions:
- **(L) locality.** Every output site `j` depends only on the inputs at a set
  `F_j ⊆ I` with `|F_j| <= K`.
- **(C) control.** Every input site `i` has a set `C_i ⊆ J` with `|C_i| <= K` such that
  `|g(u)_j - g(u')_j| < eta` for all `j in C_i` implies `|u_i - u'_i| < 1/16` (sup
  metric on `T^d`).

**Conjecture (LRSF).** For every `delta > 0` there is `beta = beta(K, d, eta, delta) > 0`
such that `|J| - |I| <= beta |I|` implies `rank g^* >= (1 - delta) d |I|` on
`H^1(T^(dJ); Z) -> H^1(T^(dI); Z)`.

A stronger *linear form* is `rank g^* >= d|I| - C(K, d, eta) d (|J| - |I|)`.

**Why it matters.** By
`sofic-torus-c2-reduces-to-rectangular-small-fibres`, LRSF
implies that every injective torus automaton over every sofic group has regular (in
fact `l^2`-injective) degree, hence is surjective.

**Known.**
- *Square case, `|J| = |I|`.* Full rank holds even without (L). This is Theorem 1 of
  `research/artifacts/lef-torus-small-fibre-2026-09-18.md`.
- *Locality one (sanity check).* If every output depends on a single input site,
  then `g` splits as a product of maps `T^d -> (T^d)^(J_i)` over disjoint `J_i`, plus
  constant outputs, and (C) forces `C_i ⊆ J_i`.
  - Theorem 1 gives full rank on every factor with `|J_i| = 1`.
  - `sum_i (|J_i| - 1) <= |J| - |I|`.
  - So the linear form holds with `C = 1`, which is sharp by Proposition S at `k = 1`.
- *Locality is necessary.* An injection `T^(N-1) -> T^N` into a small ball satisfies
  (C) with one surplus site and has `g^* = 0` ([LEF] Theorem 3).
- *The constant must grow with `K`.* Products of small-ball embeddings
  `T^k -> T^(k+1)` are `(k+1, eta_k)`-local, lose rank `k` per surplus site, and force
  `beta < 1/k` (artifact, Proposition S).
- *Square models cannot replace it beyond LEF.* Certifying every vertex of a finite
  model requires exact finite actions of the local presentation of `(W, F)`. For all
  `(W, F)` such actions exist exactly when the group is LEF
  (`exact-relation-models-give-torus-degree-regularity`).

## Attempts

- 2026-09-19 (swarm-0917-w16-w16-gs-pull, stability-approximation).
  - Section 7 of the artifact records five attempts and where each dies:
    - patchwise Theorem 1 (self-similar);
    - dimension and counting (blind to `H^1` rank);
    - local kernel vectors (no trade-off between support and surplus);
    - perturbation registers (need a modulus inequality that continuous maps lack);
    - top homology with supports (the codimension of the image is the surplus).
  - First test cases:
    - `K = 2`, `d = 1`: chains and cycles of sites;
    - the rectangular maps that Følner sets produce for amenable groups that are
      not LEF.
- 2026-09-20 (swarm-0917-w21-w21-gs-pull, reframing): zero-row slice lemma with random shared set. OPEN;
  the null-homotopic sector is closed.
  - *Established.* `zero-row-controlled-inputs-are-outnumbered`, proved in
    `research/artifacts/zero-row-slice-count-2026-09-20.md`.
    - Inputs controlled by at most `K` null-homotopic outputs number at most `c_K` times those outputs, where
      `c_K = 1/max_p (1-p)^(K-2)(1+(K-1)p)`: `c_2 = 1/2`, `c_3 = 8/9`, `c_K = 1 - 1/(2(K-1)^2) + O(K^-3)`.
    - Hence, if `g^* = 0`, the linear form holds with `C = c_(dK)/(1 - c_(dK))` for every `K` and `d`,
      **without (L)**.
    - "Locality is necessary" above therefore concerns only unbounded control sets (`K = N` there), not the
      null-homotopic sector at fixed `K`.
  - *Method.* Lift the zero rows to `R`.
    - A control set with at most one private real coordinate kills `pi_i` over every small box of the shared
      coordinates. The slices are open subsets of `R`.
    - Covering dimension (`|Z| + 1` colours, relative cup products) bounds such inputs by `|Z|`.
    - Choose the private set `T` at random with density `1/(K-1)^2`.
  - *Remaining sector.* This is in terms of w19's reduction (E_K), `|B| <= c * defect`. What is left is `B_1`:
    inputs outside the span of their control rows, with nonzero but dependent rows. For `K = 3` these are the
    proportional rows `(v, av, bv)`.
    - Restricting to the annihilator subtorus gives only `|X_T| <= D + 2 r_P - |T|`, which dies once the row
      rank `r_P` is proportional (artifact Section 5).
    - The step that is missing is a slice lemma for circle-valued shared coordinates.
