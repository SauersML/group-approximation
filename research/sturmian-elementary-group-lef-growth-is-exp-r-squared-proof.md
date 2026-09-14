---
rg: 2
id: sturmian-elementary-group-lef-growth-is-exp-r-squared-proof
kind: route
title: Two letter conditions at distance q_n ± 1 give towers with short transvections and no returns below q_(n+1); with the Rauzy-walk bound this gives exp(Θ(r^2))
target: sturmian-elementary-group-lef-growth-is-exp-r-squared
requires: [subshift-elementary-group-lef-growth-complexity-bounds]
artifacts:
  - research/artifacts/sk-lef-growth-bounds-2026-09-13-part2.md
---

The full proof is Theorem D in part 2.

- **Upper bound.** The Rauzy graph of a Sturmian subshift has `n+1` edges and cyclomatic number 2, so a covering closed walk has length `≤ 2n+2`. Item 1 of the required claim then gives `L ≤ 2^(9(8r+4)^2)`.
- **Coding.** Take `α < 1/2`. The points of `X_α` are the codings `x^±_θ` of the rotation by `α` with the arc `[1−α, 1)` (right- or left-closed).
- **Best approximation.** For `0 < t < q_(n+1)`, `‖tα‖ ≥ ‖q_n α‖`, proved from `p_(n+1) q_n − p_n q_(n+1) = ±1`.
- **Short tower.**
  - With `q_n ≤ 2m < q_(n+1)` and `s = ±q_n` chosen so that `sα ≡ −‖q_nα‖`, the set `W = {x_0 = 1, x_(1+s) = 1}` codes a half-open arc of length `ε = ‖q_nα‖`.
  - Two points of such an arc differ by less than `ε`, so `W ∩ T^t W = ∅` for `0 < |t| ≤ 2m`.
- **Cost.** `e_W = e_1 · u^(−j) e_1 u^j` with `|j| ≤ 2m+1`. So `|e_ij(e_W)| ≤ 52 + 96m`.
- **Conclusion.** Item 3 of the required claim gives `L(r) ≥ 2^(d(d−1)/2) ≥ 2^(18 m^2)` for `r ≥ 1040 + 2400m`, which is the stated lower bound.
