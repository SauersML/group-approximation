---
rg: 2
id: thompson-f-product-forest-vectors-stay-below-71-72
kind: claim
title: The product-form forest-stack test vectors for Thompson's group F cannot certify amenability; their large-window Rayleigh value is at most 71/72 for every truncation and every parameter choice
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that evaluates one member of this family (N = 80) as a lower bound 0.9397; this bounds the whole family from above, uniformly in the truncation N, so it closes that node's open proxy question.
  thompson-f-norm-bound-from-log-scale-forest-limit: that proves the family reaches at least 0.9743 in the limit; this proves it never passes 71/72 = 0.98611, so the family's supremum lies in [0.9743, 0.9862].
  thompson-f-moment-data-cannot-certify-nonamenability: that kills a class of upper-bound certificates (finite moment lists) for non-amenability; this kills a class of lower-bound certificates (a test-vector family) for amenability.
artifacts:
  - experiments/thompson-f-product-cap-2026-09-17/one_d_opt.py
  - experiments/thompson-f-product-cap-2026-09-17/one_d_opt_M9_80.out
  - experiments/thompson-f-product-cap-2026-09-17/one_d_opt_M160_1280.out
  - experiments/thompson-f-product-cap-2026-09-17/two_cell_cap.py
---

**ESTABLISHED (pen and paper).** The family is the product-form test vectors of
`thompson-f-norm-bound-from-forest-renewal-test-vector-proof`, step 4:
- a truncation `N`;
- positive split weights `phi(l,r)`, `g(l,r)` depending only on the two subtree sizes;
- positive `x_1, y_1, rho, tau`;
- `f` = (pointer-tree weight) times the product of the bulk-tree weights, on the pointed-forest
  windows `E(S_n)`.

For each parameter choice, the Rayleigh quotient `<f_n, K f_n>/<f_n, f_n>` of
`K = x_0 + x_0^{-1} + x_1 + x_1^{-1}` converges as the window size `n -> infinity`. The limit `V` satisfies

    V / 4  =  Phi(nu, eta) / 2  <=  71/72 = 0.98611...,

where `Phi(nu, eta) = BC(nu, eta)^2 + BC(nu * eta, nu)` for two probability vectors on `{1..N}`
read off from the parameters.
- Every value of `Phi` is attained: the size-only choice of the log-scale route realizes any
  positive `nu, eta`.
- So the supremum of the family over all `N` and all parameters equals `sup Phi / 2`, and lies in
  `[0.9743, 71/72]`.
- A sharper form of the same inequality gives `Phi / 2 <= 0.98596`.
- A float two-cell cap (`two_cell_cap.py`, scouting only) gives about `0.9831`.

**What dies.**
- *Invariant:* the two size laws.
  - `eta` is the renewal-tilted bulk-tree size law.
  - `nu` is the pointer-tree size law.
  - The pointer and its right neighbour are *independent* under `|f|^2`.
- *The step where the family dies:* the merge edge. The merged pointer tree has size `X + Y`, the
  sum of two independent sizes. A sum of two independent positive integers is stochastically
  larger than either summand, by a fixed amount at the median. So the merge overlap
  `BC(nu * eta, nu)` and the shift overlap `BC(nu, eta)^2` cannot both be close to 1.
- *Consequence:* the w13 open proxy ("whether `sup_N` of the ansatz optimum is `1`, that is,
  whether the optimal tree-size law escapes to infinity") is answered **no**. The optimal size law
  does escape to infinity (log-scale laws), but the value converges to at most `0.9862`, not `1`.
- *Float evidence consistent with this:* the family's optimum at finite `N` is
  `0.8777, 0.9118, 0.9290, 0.9400, 0.9475, 0.9528, 0.9567, 0.9596` at
  `N = 9, 20, 40, 80, 160, 320, 640, 1280` (`one_d_opt_M*.out`). The first four match w13's tuned
  6320-weight optimum, as the reduction predicts.

**What survives.** Test vectors whose weights correlate neighbouring tree sizes. A Følner-type
sequence must make the pointer tree and its neighbour comonotone: if `<f, K f> >= (4 - delta)||f||^2`
on pointed forests, the pointer size `s` and neighbour size `r` must satisfy
`P(s <= t < r)` and `P(r <= t < s)` both small in `delta`. Product-form vectors violate this at
the median. This condition is not proved in the graph and is recorded as a heuristic only.

**Scope.** This is a statement about one certificate family. It says nothing about `||P||` itself,
and `||P|| = 1` remains open.

Proof route: `thompson-f-product-forest-vectors-stay-below-71-72-proof`.

## Attempts
