---
rg: 2
id: fpbs-tree-projected-critical-half-graph-transfer-below-one
kind: claim
title: The critical half-graph transfer matrix of a tree-projected Cayley graph is contracting
distinct_from:
  fpbs-hyperbolic-quotient-uniform-fibre-bubble: that asks for a uniform bound on the whole fibre bubble below p_c over any hyperbolic quotient; this asks, on tree-projected generating sets, for finite critical fibre susceptibility and a contracting non-backtracking matrix of squared half-graph branching factors.
  fpbs-amenable-wq-normal-relative-subcriticality: that asks for finite relative susceptibility at some p above p_c; this is a strict quantitative condition at p_c on half-graph factors.
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
* **Numerical signal.**
  * *Method and data.* The Monte Carlo `experiments/fpbs-tree-projected-mc/tpmc.c`
    ran on MSI, coarse scan, `N = 2000`. At parameters with no truncated cluster
    the row-sum bound on `rho(N_p)` was:
    * at most 0.31 on `T_4 □ Z` at `p = 0.20` (`chi_p ≈ 24`);
    * at most 0.20 with fibre steps `1..5` at `p = 0.08` (`chi_p ≈ 14`);
    * at most 0.75 with `a`-heights `{0,1,2,3}` at `p = 0.10` (`chi_p ≈ 53`).
  * **Where it stops:** these are monotone lower bounds for the critical
    values, the factors still grow toward `p_c`, and numerics are evidence
    only.
