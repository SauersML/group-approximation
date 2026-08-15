---
rg: 2
id: kazhdan-projection-finite-target-calculus-proof
kind: route
title: Uniform spectral gap, polar cancellation, and equivalent projections
target: kazhdan-projection-finite-target-calculus
requires: []
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

## Direct proof

**The projection.**  Choose a finite symmetric Kazhdan set `S` with
constant `kappa` and put `a = (1 + T)/2` for the averaged generator
`T = |S|^{-1} sum_{s in S} s` in `C*_max(L)`.  In every unitary
representation, `a` acts as `1` on the fixed vectors, while on their
complement a unit vector is `kappa`-displaced by some generator, giving
`<pi(a) xi, xi> <= 1 - kappa^2/(4|S|)`.  So uniformly over all
representations `sp(pi(a)) <= [0, 1 - delta] cup {1}` with
`delta = kappa^2/(4|S|) > 0`; hence `a^n` converges in the maximal norm to
a projection `p in C*_max(L)` acting in every representation as the
orthogonal projection onto the fixed vectors.  Let `p_L` be its image
in `A`, and represent `A` faithfully on a Hilbert space: `p_L` projects
onto the `rho(L)`-fixed vectors.

**Clause 1.**  `q = rho(s) p_L rho(s)^*` projects onto the
`rho(sLs^{-1})`-fixed vectors, and `sLs^{-1} <= L` gives `p_L <= q`.  Put
`v = rho(s) p_L`; then `v^* v = p_L` and `v v^* = q`, so
`w = v^* + (1 - q)` satisfies `w^* w = 1` and `w w^* = p_L + (1 - q)`.
Finiteness makes the isometry `w` unitary, forcing `p_L + (1 - q) = 1`,
i.e. `p_L = q`.

**Clause 2.**  For `L` normal, `rho(h) p_L rho(h)^*` and `p_L` both
project onto the fixed vectors of `rho(hLh^{-1}) = rho(L)`.

**Clause 3.**  Every `rho(l)` fixes the range of `p_L`; if `p_L = 1` the
range is everything.

**Finiteness of the targets.**  In a norm matrix corona or norm
ultraproduct, `x^* x = 1` lifts to `‖x_n^* x_n - 1‖ -> 0`; eventually
`x_n` is invertible and its polar correction is unitary at vanishing
distance, so `x` is unitary.

**Audit note (this session).**  Checked: the uniform gap estimate, the
convergence of `a^n` in the maximal norm (uniform spectral containment),
the equivalent-projection cancellation, and the polar-correction
finiteness — the last two are the arguments already printed in the
manuscript's transport proof, here isolated as the reusable engine.
