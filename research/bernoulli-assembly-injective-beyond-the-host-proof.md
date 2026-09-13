---
rg: 2
id: bernoulli-assembly-injective-beyond-the-host-proof
kind: route
title: Orbit representations at finite-support configurations give unitriangular rank functionals on the cylinder classes
target: bernoulli-assembly-injective-beyond-the-host
requires:
  - bernoulli-bc-splits-into-host-and-cylinder-comparison
artifacts: [research/artifacts/bc-bernoulli-rank-functionals-2026-09-13.md]
---

Full proofs are in Sections 1--2 of the artifact.

- **R1 (compacts).** Take `f ∈ C_c(X \ {0})`. It is supported in finitely many `U_z = {y_z ≠ 0}`. Then `f(h^(-1)x) ≠ 0`
  allows at most `m |supp x|` elements `h`, because the action is free. So `π_x(f)` has finite rank, and `π_x` maps
  `I_1 ⋊_r G` into the compacts.
- **R2 (counting).** `π_x(1_(C_s))` is the diagonal projection onto `{δ_h : h·s <= x}`. The map `h ↦ h·s` is
  injective, since `G` is torsion-free and `Z` free.
- **R3 (injectivity).** Suppose `T_r(m) = 0`, and choose `[s']` with `m_([s']) ≠ 0` and `|F_(s')|` minimal. At
  `x = x_(s')`, `r_x(T_r m) = Σ_(t <= x) m_([t]) = m_([s'])`. So `m = 0`. In degree 1 the source is `0`.
- **R4.** Items 1, 3 and 6 of `bernoulli-bc-splits-into-host-and-cylinder-comparison` turn R3 into injectivity of
  `mu_(G, I_1)`, and into the equivalence of injectivity for `F_p wr_Z G` and for `G`.
- **R5 (expansion).** Möbius inversion over the Boolean lattice of sub-patterns defines `n(y)`.
- **R6 (truncation).** Take the quotient `I_1 -> C_0(P_k)`, `P_k = {1 <= |supp| < k}`.
  - `C_0(P_k)` is filtered by the proper strata `c_0(S_j)`. Equality of maximal and reduced crossed products passes to
    extensions, so the Lemma E of the prior artifact makes the sequence exact.
  - `K_0(C_0(P_k) ⋊_r G) = ⊕_(|F|<k) Z` is detected by the `r_x` with `|supp x| < k`.
  - So `y - T_r(n^(<k)(y))` maps to `0` there and comes from `K_0(I_k ⋊_r G)`.
- **R7 (additivity).** Approximate a projection `p` within `1/4` by a self-adjoint locally constant `a`, with group
  support `E ∋ e` and coordinate window `W`. Put `B = W^(-1) E E^(-1) W ∪ W^(-1) W`.
  - If `supp x_2 ∩ (supp x_1)·B = ∅`, then `π_(x_1+x_2)(a) = π_(x_1)(a) + π_(x_2)(a)` with orthogonal supports.
  - Spectral projections at `1/2` have the ranks of `π_x(p)`, so `r_(x_1+x_2) = r_(x_1) + r_(x_2)`.
  - The alternating sums then kill the Möbius coefficients of `B`-disconnected patterns.
- **R8 (three shapes).** If `n(y)` is infinitely supported, R7 gives shape (a). If `n(y)` is finitely supported and
  `y ∉ im T_r`, the remainder `y - T_r(n(y))` is rank-invisible and, by R6, lies in every `im K_0(I_k ⋊_r G)`: shape
  (b). Degree 1 is shape (c).

**Context, not re-read:** exactness of maximal crossed products, Green imprimitivity, and the fact that close
projections have equal rank. QED.
