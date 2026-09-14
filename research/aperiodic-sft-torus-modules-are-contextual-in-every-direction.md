---
rg: 2
id: aperiodic-sft-torus-modules-are-contextual-in-every-direction
kind: claim
title: Every nonzero torus tiling module of an aperiodic Z^2 SFT has noncommuting site idempotents inside a narrow strip along every rational direction, separated by more than 2D along the strip
distinct_from:
  periodic-quantum-tilings-refute-quantum-rigidity: that shows a periodic quantum tiling is noncommutative with no one-dimensional composition factor; this locates the noncommutation inside narrow strips along every rational direction
  sft-tiling-module-dimensions-and-periods-must-diverge: that forces unbounded dimensions and period tori; this forces directional contextuality at every scale on any torus
artifacts:
  - research/artifacts/sk-labbe-2d-strip-contextuality-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.** `Ω ⊆ A^(Z^2)` is an aperiodic SFT with forbidden patterns in `B_r`, `D >= r`, `Λ ≤ Z^2` of finite index, `k` any field, and `V != 0` a module of `𝒯_(D,Λ)(Ω,k)` (`torus-quantum-tilings-decide-matriciality-of-sft-rings`), of any dimension.

**Statement.** For every primitive `e = (p,q)`, with `ℓ_e(z) = q z_1 − p z_2`, there are:
- sites `t, t'` and letters `a, b` with `e_a(t) e_b(t') != e_b(t') e_a(t)`;
- representatives `z ∈ t`, `z' ∈ t'` with `|ℓ_e(z) − ℓ_e(z')| <= 2r(|p|+|q|)`;
- and no representative of `t' − t` in `B_(2D)`.

**Covariant families over a finite field.** Every strip `{c <= ℓ_e(z) <= c + 2r(|p|+|q|)}` generates a noncommutative algebra, for every `e` and every `c`.

**For Labbé's `Ω_U` (`r = 1`).**
- Any witness for `labbe-wang-shift-crossed-product-is-exactly-matricial` at any scale `D` has contextual pairs inside vertical and horizontal strips of width `3`, and inside diagonal strips of `ℓ_e`-width `5`, …, each at sup-distance `> 2D`.
- Covariant witnesses have them in every such strip.
- The noncommutation is carried by holonomy around the rational cycles of narrow annuli, for all directions at once.

Route: `aperiodic-sft-torus-modules-contextual-every-direction-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part4.md`):** PASS (§6). Note W9: Corollary D needs finite-dimensional families, so that U^e has finite order.
