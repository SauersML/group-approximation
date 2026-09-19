# One-level projection for the overfold exchange (O)

Target: `fpbs-mal-overfold-merges-never-help` (O): `deep_j(Q) = law_j(Q)`.
Experiments: `experiments/fpbs-overfold-projection-2026-09-17/`.

## Setting

- `Γ = Γ_{j+1}(Q)`. For `i ≤ j` let `p_i : Γ → Γ_i(Q)` be the map to the
  folded `L_i`-graph. `m = p_j`, and `p_1` factors through `m` (`j ≥ 1`),
  so `ker m ⊆ ker p_1`.
- A seed is a same-fibre pair `(x, y)`. It has **level ≥ i** iff
  `p_i(x) = p_i(y)`. Level 0 means the images in `C_1` already differ.
- `cl(P)` is the fold closure of `P`. A **hit** is a `P` with
  `cl(P) ⊇ ker m`.
- `ker p_1` is fold-closed, because `Γ_1(Q)` is folded. Level ≥ 1 pairs
  split into **blocks**: the components of the relation
  `(x, y) — (x·e, y·e)`. A fold-closed family that contains one pair of a
  block contains the whole block. So `cl(P) ∩ ker p_1` is the closure of
  the blocks it contains.
- `ℓ_1(P)` is the least number of level ≥ 1 seeds whose closure contains
  `cl(P) ∩ ker p_1`.

## Statements

- **(O'-rel).** `ℓ_1(P) ≤ |P|` for every finite seed set `P`.
- **(Z1).** If `P` contains a level-0 seed, then `ℓ_1(P) ≤ |P| − 1`.

(Z1) ⇒ (O'-rel). If every seed of `P` has level ≥ 1, then
`cl(P) ⊆ ker p_1`, and so `ℓ_1(P) ≤ |P|` holds trivially.

At `j = 1`, level ≥ 1 is the lawful type, so (O'-rel) is exactly (O-rel)
of the w17 decomposition. For `j ≥ 2` the two statements are not
comparable a priori:
- (O'-rel) allows every level ≥ 1 seed as a replacement, but must cover
  the larger family `ker p_1`;
- (O-rel) must cover only `ker m`, but may use lawful seeds only.

## Proved: (O'-rel) ⇒ (O'_j) ⇒ (O) on transitive levels, j ≤ 4

**Lemma 1.** (O'-rel) at depth `j` implies `deep_j(Q) = deep_j^{≥1}(Q)`
for every finite `Q`.

*Proof.* Let `P` be a hit with `|P| = deep_j(Q)`. Then
`ker m ⊆ cl(P) ∩ ker p_1`. By (O'-rel) there are at most `|P|` level ≥ 1
seeds whose closure contains `cl(P) ∩ ker p_1 ⊇ ker m`. These seeds form
a hit. So `deep_j^{≥1} ≤ deep_j`. The reverse inequality is trivial. ∎

**Corollary 2.** Assume (O'-rel) holds at depths `1, …, j` with `j ≤ 4`.
Then (O) holds at `(j, Q)` for every `L_{j+1}`-transitive `Q`.

*Proof.* Use induction on `j`. The base `j = 0` is trivial, since every
seed is lawful there. For the step, apply Corollary R of
`research/artifacts/fpbs-overfold-depth-shift-reduction-2026-09-19.md`.
Its input (O'_j) is Lemma 1. It also chains Lemma D, which is proved for
`j ≤ 4` via (T_j), with (O) at `(j − 1, Q^{(1)})`. `Q^{(1)}` is
`L_j`-transitive, so the induction hypothesis applies to it. ∎

So, on transitive levels with `j ≤ 4`, (O) now follows from one
statement per depth. That statement is purely one-level: it compares
level-0 seeds with level ≥ 1 seeds only. The finer levels 1..j do not
appear. It is also a statement about **all** seed sets, so it can be
attacked by induction on `|P|`. This matches the "(O-rel) instead of (F)"
design of the w17 decomposition.

## Computed, not proved: (Z1) for |P| = 1

**Observation 3.** A single level-0 seed `s` has `ℓ_1({s}) = 0` (that
is, `cl(s) ∩ ker p_1` is trivial) whenever no point of `Q` is fixed by
both `a` and `b`. The hypothesis on fixed points is needed.

Data, from `single_seed.py` (outputs `single_j1.txt`, `single_j2.txt`),
testing every level-0 seed on random `Q`:
- `j = 1`, `n ≤ 9`, 400 levels: 42,063 seeds;
- `j = 2`, `n ≤ 7`, 200 levels: 103,228 seeds.

There are 422 failures. Every one of them occurs on a level that has a
common fixed point of `a` and `b`. The transitive failures are exactly
the levels with `n = 1`.

Heuristic only: level-0 types are trees with at most 3 vertices, and a
same-layer merge seems to need the three layer pairs of one fibre to
close up. A proof has to control the extra folds that the equivalence
closure forces where `C_{j+1}` is incomplete. That is not done here.

## Computed: (Z1) and (O'-rel) for |P| ≥ 2

No violation of either statement was found. All files named below are in
the experiments directory.

- `oprime.py` computes exact seed numbers. Runs:
  - `op_j2_n7_lvl0.txt`: level-0 seeds only, `j = 2`;
  - `op_j2_n7_mixed.txt` and `op_j2_n6_mixed_slack.txt`: seeds of mixed
    levels, `j = 2`.
  - Result: 0 violations, and 0 `NO-SLACK` cases (so every tested `P`
    satisfies (Z1)).
- `oprime_climb.py` runs hill-climbs over sets of `k` level-0 seeds,
  maximising `ℓ_1`. Each run has 0 violations.

  | file | j | n | k | best `ℓ_1` |
  |---|---|---|---|---|
  | `climb_j1_n8_k3.txt` | 1 | 8 | 3 | 2 (greedy) |
  | `climb_j2_n6_k4.txt` | 2 | 6 | 4 | 3 (exact) |
  | `climb_j3_n4_k4.txt` | 3 | 4 | 4 | 3 (exact) |
  | `climb_j2_n7_k6.txt` | 2 | 7 | 6 | 5 (exact) |

- `slaw.py` tests (S_law). **(S_law) is (O-rel) of the w17 decomposition,
  restated; it is not new.** Result: 0 violations
  (`slaw_j1_n10_over.txt`, `slaw_j2_n7_over.txt`).

## Obstruction: the bound |P| − 1 is attained

The climbs reach `ℓ_1 = k − 1` exactly at `k = 4, 6` (at `k = 3` only the greedy
upper bound 2 is known). So a level-0 seed can be worth as much as a
level ≥ 1 seed, minus one in total.

- **Refuted:** `ℓ_1(P) ≤ ⌈|P|/2⌉`. The exact values are `ℓ_1 = 3` at
  `k = 4` and `ℓ_1 = 5` at `k = 6`.
- **Consequence for proofs.** A proof of (O'-rel) that charges each
  level-0 seed a fixed weight `c < 1` has to lose `(1 − c)|P|`. That loss
  is incompatible with these examples once `(1 − c)k > 1`. The data do
  not support a bound `ℓ_1 ≤ c|P| + C` with `c < 1`. This is evidence at
  `k ≤ 6`, not a proof for all `k`.
- **What is left.** An exact exchange: remove one level-0 seed and pay
  at most one level ≥ 1 seed. This is (O-step) of the w17 decomposition,
  projected to one level.

## Open

- (Z1) and (O'-rel) for all `|P| ≥ 1`. For `|P| = 1` there are only the
  data of Observation 3.
- Levels `Q` that are not `L_{j+1}`-transitive, and depths `j ≥ 5`.
  These limits are inherited from Lemma D.
