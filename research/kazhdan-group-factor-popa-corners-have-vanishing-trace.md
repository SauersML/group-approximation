---
rg: 2
id: kazhdan-group-factor-popa-corners-have-vanishing-trace
kind: claim
title: In the group factor of an ICC Kazhdan group, finite-dimensional Popa corners serving approximate Kazhdan generators have trace O((eta+delta)^2)
distinct_from:
  property-t-factors-contain-weakly-dense-popa-algebras: that is the existence question for weakly dense Popa algebras in property (T) factors; this is a necessary scale condition on any example in a property (T) group factor.
  separable-ii1-factors-have-weakly-dense-full-free-group-cstar: that constructs weakly dense residually finite-dimensional subalgebras in every separable II_1 factor; this constrains where finite-dimensional compressions of weakly dense subalgebras can live when the factor has property (T).
artifacts:
  - research/artifacts/sk-free-5-brown-q3-2026-09-13-part1.md
  - research/artifacts/sk-verify-14-2026-09-13-part5.md
---

**ESTABLISHED (unreviewed, lane sk-free-5, 2026-09-13)** by route `kazhdan-group-factor-popa-corners-vanishing-trace-proof`.

Let `G` be an ICC group with property (T), `(S, ε_S)` a Kazhdan pair, `M = L(G)` with trace `τ`, and `A ⊆ M` a C*-subalgebra. Suppose:
- `y_s ∈ A` satisfy `‖y_s − λ_s‖_2 ≤ δ` for `s ∈ S`;
- `p ∈ A` is a nonzero projection, and `B ⊆ pAp` is a finite-dimensional C*-subalgebra with unit `p`;
- for every `s ∈ S`, `‖[p, y_s]‖ ≤ η` and `dist(py_sp, B) ≤ η`, in operator norm.

Then

`τ(p) ≤ 4 ε_S^{-2} (4η + 2δ)²`.

**Consequence for Brown's Question 3 (Popa clause).** Let `A ⊆ L(G)` be a weakly dense Popa algebra, in the Brown–Dykema definition (arXiv:math/0207005, introduction).
- Fix `δ`. Kaplansky density gives `y_s ∈ A` that are `δ`-close to `λ_s` in 2-norm.
- Every Popa corner for `{y_s}` at tolerance `η` then has trace at most `4ε_S^{-2}(4η + 2δ)²`.
- So a weakly dense Popa algebra in a property (T) group factor must hide its finite-dimensional structure on corners of vanishing trace, as Brown–Dykema's algebras in `L(F_s)` do.
- In particular `L(G_X)` (`subshift-elementary-groups-are-character-rigid`, ICC because it is infinite and simple) is subject to this bound.

The same argument works in any full II_1 factor, with a spectral-gap set in place of `λ(S)` (Connes 1974, recalled, locator not checked).

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived: the spectral-gap inequality (SG) from ICC, the half-trace projection `e ∈ B′ ∩ pMp`, `‖[e, y_s]‖ ≤ 4η`, and `τ(e)(1 − τ(e)) ≥ τ(p)/4`. The extension to full factors through Connes's spectral-gap sets is recalled, not checked. See `research/artifacts/sk-verify-14-2026-09-13-part5.md` §3.
