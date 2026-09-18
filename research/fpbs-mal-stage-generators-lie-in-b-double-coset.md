---
rg: 2
id: fpbs-mal-stage-generators-lie-in-b-double-coset
kind: claim
title: For Gamma_mal, every single element that generates a stage H_m over an earlier stage H_n lies in H_n b_m^{±1} H_n
distinct_from:
  fpbs-malnormal-coset-cycles-linear-perimeter: that bounds packing certificates for generators already known to lie in H_n b_m^{±1} H_n; this proves that every generator of the stage pair lies there, a purely group-theoretic statement about Stallings graphs.
  fpbs-mal-long-generator-packing-growth: that asks for long generators outside the double coset with small packing floors; this shows no generator lies outside the double coset.
artifacts:
  - research/artifacts/fpbs-mal-stage-generator-rigidity-2026-09-17.md
  - experiments/mal-long-generator-packing-2026-09-17/vertex_pairs.py
  - experiments/mal-long-generator-packing-2026-09-17/local_closure.py
  - experiments/mal-long-generator-packing-2026-09-17/dumbbell.py
---

**ESTABLISHED.** In `Gamma_mal = U_m H_m`, let `H_m` be free on `{a, b_m}` with
`b_{m-1} = b_m a b_m^{-2}`. Then for all `n < m` and `t ∈ H_m`,

    <H_n, t> = H_m   implies   t ∈ H_n b_m H_n ∪ H_n b_m^{-1} H_n.

**Proof outline.** Full proof in the artifact.
1. **Lemma 1.** If `<H, t> = F` for `H != F`, then `t ∈ H g_p g_q^{-1} H` for
   vertices `p != q` of the Stallings graph whose identification folds to the
   rose.
2. **Lemma 2.** Such generating pairs descend along the morphism
   `Δ_{d+1} -> Δ_d` of the stage Stallings graphs, where `d = m - n`.
3. **Lemma 3.** `Δ_d` is a dumbbell with bridge `β_{d+1} = β_d λ_d` and loop
   `λ_{d+1} = β_d^{-1} a β_d λ_d^{-1}`.
4. **Proposition 4.** For `d >= 2`, the only generating pairs are
   `(0, 0b)`, `(0, 0ba)` and their reverses.
   - **Base.** `d <= 5`, by exact computation.
   - **Step.** Each of the 16 non-target lifts of these pairs to `Δ_{d+1}`
     closes after at most 3 vertex merges inside a local model that avoids its
     boundary. So none of them folds to the rose.

**Not claimed.** Nothing about generating sets of size `>= 2`, or about pairs
`(H_m, K)` for subgroups `K` other than stages.

## Attempts
