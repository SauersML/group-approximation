---
rg: 2
id: sp21-golod-shafarevich-test-proof
kind: route
title: Presentation bound from mod-p cohomology, Golod-Shafarevich-Vinberg, then Zelmanov's free subgroups
target: sp21-golod-shafarevich-test-gives-infinite-pro-p-rank
requires: []
artifacts:
  - research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md
---

**Imported inputs (statements only; the sources were not re-read here).**
- **(H)** For any finitely generated group `Δ`, `H^1(Δ̂_p;F_p) = H^1(Δ;F_p)`, and
  `H^2(Δ̂_p;F_p) -> H^2(Δ;F_p)` is injective. So `Δ̂_p` has a pro-p presentation
  with `d` generators and at most `dim H^2(Δ;F_p)` relations.
- **(GSV)** Golod–Shafarevich–Vinberg: if a pro-p group has a presentation with
  `d >= 3` generators and `r` relations, and `1 - d t + r t^2 < 0` for some
  `t ∈ (0,1)`, then it is infinite. When `r < d^2/4`, `t = 2/d` works.
- **(Z)** Zelmanov: such a Golod–Shafarevich pro-p group contains a non-abelian
  free pro-p subgroup.

**Proof.**
- **Case `d = 2`.** The bound forces `r = 0`, so `Δ̂_p` is free pro-p of rank `2`.
- **Case `d >= 3`.** (H) and (GSV) make `Δ̂_p` Golod–Shafarevich, and (Z) gives a
  free pro-p subgroup `F` of rank `>= 2`.
- **Conclusion.** Open subgroups of index `p^n` in `F` have rank
  `1 + p^n(rank F - 1)` (Schreier), which is unbounded. A finite-rank group has
  all closed subgroups of bounded rank, so `Δ̂_p` has infinite rank. ∎
