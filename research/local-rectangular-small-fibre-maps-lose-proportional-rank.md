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
- 2026-09-19 (swarm-0917-w19-w19-gs-break, minimal-counterexample).
  - **The first test case is closed.** At `d = 1` with `|C_i| <= 2`, the linear form
    holds with the sharp constant `C = 1` and **without (L)**:
    `rank g^* >= 2|I| - |J|`. See
    `two-output-control-circle-maps-lose-rank-at-most-surplus` and
    `research/artifacts/two-output-control-rank-2026-09-19.md`.
  - The proof has three steps:
    - glue the coarse inverse into `psi_i` on a neighbourhood `U_i` of the image in
      `T^(C_i)`;
    - use `H^2(U_i) = 0` when `U_i` is not all of `T^2`, so the input is in the span of
      its control rows or both control rows are zero;
    - show that two such inputs cannot share a zero row, because the level strips of
      that row's real lift kill both classes, a two-set Lusternik–Schnirelmann cover.
  - **Correction to "Locality is necessary".** The cited [LEF] Theorem 3 map needs
    `|C_i| = N`, so it violates (C) for every fixed `K`. Whether (L) is needed once
    `|C_i| <= K` is open for `K >= 3`, and it is not needed at `K = 2`.
  - **General `K`, `d = 1` (Lemma D_K).** Either `pi_i` is in the span of its control
    rows, or those rows have rank `<= |C_i| - 2`. The linear form, with
    `C = c_K / (1 - c_K)`, follows from the counting inequality
    `(E_K): |B| <= c_K defect(∪_(i in B) C_i)` for some `c_K < 1`.
    - Proposition S forces `c_K >= (K-1)/K`.
    - (E_K) is open for `K >= 3`. Lemma L uses one shared real function, and it dies
      when a slice of `U_i` is 2-dimensional (tori of revolution).
