---
rg: 2
id: fpbs-tree-projected-critical-half-graph-transfer-below-one
kind: claim
title: The critical half-graph transfer matrix of a tree-projected Cayley graph is contracting
distinct_from:
  fpbs-hyperbolic-quotient-uniform-fibre-bubble: that asks for a uniform bound on the whole fibre bubble below p_c over any hyperbolic quotient; this asks, on tree-projected generating sets, for finite critical fibre susceptibility and a contracting non-backtracking matrix of squared half-graph branching factors.
  fpbs-amenable-wq-normal-relative-subcriticality: that asks for finite relative susceptibility at some p above p_c; this is a strict quantitative condition at p_c on half-graph factors.
artifacts:
  - research/artifacts/fpbs/docs/tree-projected-branching-numerics-2026-09-12.md
---

**OPEN.** Let `Gamma` be finitely generated with an infinite cyclic normal
subgroup `H` and `Gamma/H ≅ F_n`, `n >= 2`. Let `S` be a finite symmetric
generating set whose image lies in `{1} ∪ B ∪ B^(-1)` for a free basis `B`.
With `chi^H_p` and `lambda_p(s) = p m_s chi^(s)_p` as in
`fpbs-tree-projected-branch-share-last-crossing-bound`, taking left limits at
`p_c`:

```text
chi^H_(p_c) < infinity   and   rho(N_(p_c)) < 1,
where N_p(s,t) = lambda_p(t)^2 1{t != s^(-1)}  over letters s, t.
```

A sufficient form is `(2n-1) max_s lambda_(p_c)(s)^2 < 1`. By item 4 of that
claim, this makes the critical fibre-sphere bubble decay geometrically.

## Attempts

* **Mean-field prediction.**
  * *What it predicts.* A critical branching random walk on the tree of fibres
    has half-graph factors about `1/(2n-1)` and transient projected walk. So
    `rho(N_(p_c))` should be about `1/(2n-1)` and `chi^H_(p_c)` finite.
  * **Where it stops:** it is a triangle-type comparison, which is not available
    on these unimodular graphs.
* **Contradiction from a large factor.**
  * **Where it dies:** FKG lower bounds exist only for products of fibre maxima.
    Summing products of two-point functions over intermediate points
    overcounts, so no lower bound of the form `prod lambda_p(s_j)` for fibre
    masses is available. A large `lambda_p(s)` below `p_c` contradicts nothing.
* **Radius one (dead).** It would be simplest to show `b_1(p_c) < 1` directly.
  **Where it dies:** numerically `b_1 > 1` already below `p_c` on all four test
  graphs: 1.19 on `T_4 □ Z`, 1.32 on `(a,0),(a,1),(b,0),(1,1)`, 6.7 with fibre
  steps `1..5`. So any finite-radius target needs `R >= 2`. This is the reason
  for going through the transfer matrix.
* **First-hit nearest-fibre bound (dead on one graph).** Artifact Section 4.3
  of `fibre-summed-hyperbolic-quotient-criterion.md` asks for
  `sup_(p<p_c) max_s sigma_p(s) < 1`. **Where it dies:** with fibre steps `1..5`,
  at a capped-free parameter below `p_c`, `sigma(b) = 1.38 ± 0.05`.
* **Numerical signal.**
  * *Method.* `experiments/fpbs-tree-projected-mc/tpmc.c`, run on MSI.
  * *Results.* At the largest capped-free parameters of four graphs, `rho(N_p)`
    lies between 0.37 and 0.47 and `chi^H_p` between 1.6 and 4.2. On the
    asymmetric example `rho` rises slowly: 0.31, 0.35, 0.38, 0.40, while
    `chi_p` grows from 18 to 90. Details are in the artifact.
  * **Where it stops:** these are monotone lower bounds for the critical
    values, and numerics are evidence, not proof.
