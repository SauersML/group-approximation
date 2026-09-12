---
rg: 2
id: log-depth-rate-unit-type-equivalence-proof
kind: route
title: Rate gives unit type by the log-depth bound, unit type has depth zero, and shallow mass always vanishes
target: log-depth-rate-rounding-is-equivalent-to-unit-type
requires:
  - nonunit-root-mass-log-depth-scale-bound
  - compressor-transport-exactifies-under-vertex-rounding
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - nonunit-projection-bounded-by-root-spectral-mass
artifacts:
  - research/artifacts/nh-log-depth-rate-2026-09-12.md
---

Fix `σ`. All limits are along `U`.

**(a) ⟹ (b).** Item 3 of `nonunit-root-mass-log-depth-scale-bound` gives `τ(1 - P_n) -> 0` for the
rate roundings. Replace the constituents of `π_n` that are nontrivial on `St_r(A_nu)` by the trivial
representation. On each generator this moves `π_n` by at most `2·τ(1 - P_n)^(1/2)` in normalized 2-norm.
So the result is still an (H1) rounding, and it factors through `St_r(A_u)`, where every `x_i` is a
unit. That is (b). This is the existing route `unit-type-rounding-via-log-depth-rate`.

**(b) ⟹ (a).** Let `π_n` factor through `St_r(R_+/I_n)` with every `x_i` a unit. Then `A_nu = 0`, so
every root character `χ` has trivial non-unit component, `depth_nu(χ) = 0`, and `D(π_n) = 0`. The defect
`δ_n` is a normalized 2-norm distance between unitaries, so `δ_n <= 2`. Hence
`δ_n^2 log(1 + D(π_n)) = 0` for every `n` and any unitary representatives of `σ_n(A)`.

**(b) ⟹ (c).** As above, `χ_nu` is trivial on the support of `μ_n`, so `μ_n(depth_nu > 1) = 0`.

**(c) ⟹ (b).** Let `π_n` be (H1) roundings with `μ_n(depth_nu > 1) -> 0`.
- Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` gives
  `μ_n(depth_nu = 1) <= q·η_n + η_n^t` for every (H1) rounding. This tends to 0: `η_n -> 0` by item 1 of
  `compressor-transport-exactifies-under-vertex-rounding`, and `η_n^t -> 0` by item 2 of the shallow claim.
- `nonunit-projection-bounded-by-root-spectral-mass` gives
  `τ(1 - P_n) <= r(r-1)·[μ_n(depth_nu = 1) + μ_n(depth_nu > 1)] -> 0`.
- Replace the non-unit constituents by the trivial representation as in (a) ⟹ (b).

Only established inputs are used. Nothing about `G` beyond `σ(A)` and the torus block already inside those
inputs enters. Neither (a), (b) nor (c) is established by this route: it establishes only the equivalence.
