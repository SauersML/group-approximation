---
rg: 2
id: fpbs-mal-stage-generators-lie-in-b-double-coset-proof
kind: route
title: Generating elements are vertex identifications of the dumbbell Stallings graph, and only two survive the descent
target: fpbs-mal-stage-generators-lie-in-b-double-coset
requires: []
artifacts:
  - research/artifacts/fpbs-mal-stage-generator-rigidity-2026-09-17.md
  - experiments/mal-long-generator-packing-2026-09-17/fg.py
  - experiments/mal-long-generator-packing-2026-09-17/packing.py
  - experiments/mal-long-generator-packing-2026-09-17/vertex_pairs.py
  - experiments/mal-long-generator-packing-2026-09-17/pairs_show.py
  - experiments/mal-long-generator-packing-2026-09-17/dumbbell.py
  - experiments/mal-long-generator-packing-2026-09-17/local_closure.py
  - experiments/mal-long-generator-packing-2026-09-17/gens_census.py
---

The complete proof is in
`research/artifacts/fpbs-mal-stage-generator-rigidity-2026-09-17.md`, §1–§5.

1. **Lemma 1 (§1).** If `<H, t> = F` and `H != F`, then there is a vertex pair
   `(p, q)` of the Stallings graph `Δ` of `H` such that:
   - `t ∈ H g_p g_q^{-1} H`;
   - `Δ/(p ~ q)` folds to the rose.

   *Proof.* Read the maximal prefix and suffix of `t` in `Δ`. If they do not
   overlap, no vertices of `Δ` are identified.
2. **Lemma 2 (§2).** Generating pairs descend along the stage morphism
   `π: Δ_{d+1} -> Δ_d`.
3. **Lemma 3 (§3).** `Δ_d` is a dumbbell with the Pell-length recurrence. The
   proof is by induction and is machine-checked for `d <= 7`.
4. **Proposition 4 (§4).** For `d >= 2`, the generating pairs are
   `(0, 0b), (0, 0ba)` and their reverses. Every generating pair gives an
   element of `H b^{±1} H`.
   - **Base.** `d = 1..5` by `vertex_pairs.py 5`.
   - **Step.** For `d >= 3`, the fibres of `π` over `0, 0b, 0ba` have 3
     elements each. Of the 18 lifts, the 16 non-target ones close inside the
     local model (`local_closure.py`, with two closures also checked by hand).
     Each uses at most 3 merges, while `|V| >= 49`.
5. **Theorem (§5).** Lemma 1 and Proposition 4 together.
