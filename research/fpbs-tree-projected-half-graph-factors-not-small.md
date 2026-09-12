---
rg: 2
id: fpbs-tree-projected-half-graph-factors-not-small
kind: claim
title: At criticality the unsquared half-graph transfer matrix is at least critical unless the fibre susceptibility diverges
distinct_from:
  fpbs-tree-projected-critical-half-graph-transfer-below-one: that is the open sufficient condition rho(N_(p_c)) < 1 on squared half-graph factors; this is a necessary lower bound rho(M_(p_c)) >= 1 on unsquared factors, which confines any proof of that condition to a window.
  fpbs-tree-projected-branch-share-last-crossing-bound: that bounds fibre masses above by products of half-graph factors; this sums that bound over the whole quotient against the divergence of the susceptibility at p_c.
---

**ESTABLISHED.** Use the setting and notation of
`fpbs-tree-projected-branch-share-last-crossing-bound`:
* `pi : Gamma -> F_n`, and `S` a generating set projecting into
  `{1} ∪ B ∪ B^(-1)`;
* `chi^H_p`, `chi^(s)_p` and `lambda_p(s) = p m_s chi^(s)_p`, with values at
  `p_c` taken as left limits.

Define the non-backtracking matrix over letters
`M_p(s,t) = lambda_p(t) 1{t != s^(-1)}`. Then

```text
chi^H_(p_c) = infinity     or     rho(M_(p_c)) >= 1.
```

**Consequences.**
* **Graphs with the L2 gap.** Let `H` be amenable and `p_c < p_{2->2}`. By
  `fpbs-fibre-summed-connectivity-operator`,
  `chi^H_(p_c) <= ||S_(p_c)|| = ||T_(p_c)|| < infinity`. So `rho(M_(p_c)) >= 1`.
* **Uniform factors.** Suppose `lambda_(p_c)(s) = lambda` for every letter. Then
  `rho(M) = (2n-1) lambda` and `rho(N) = (2n-1) lambda^2`. Finite fibre
  susceptibility forces `lambda >= 1/(2n-1)`, while
  `fpbs-tree-projected-critical-half-graph-transfer-below-one` asks for
  `lambda < 1/sqrt(2n-1)`. The target therefore sits in the window
  `[1/(2n-1), 1/sqrt(2n-1))`.
* **What no proof can do.** No argument can bound every critical half-graph
  factor below `1/(2n-1)`, or more generally make the unsquared transfer matrix
  contracting at `p_c`. Any proof of the critical estimate has to use the
  squaring in the sphere bubble, that is, the L2 structure rather than
  one-sided branching.

**Numerical consistency.** On `(a,0),(a,1),(b,0),(1,1)` at `p = 0.156`, the
measured factors `lambda(a) = 0.471` and `lambda(b) = 0.255` give
`rho(M) ≈ 1.06` and `rho(N) ≈ 0.40`. Both values are lower bounds for the
critical left limits, and they sit in the window.

Proof: `fpbs-tree-projected-half-graph-factors-not-small-proof`.
