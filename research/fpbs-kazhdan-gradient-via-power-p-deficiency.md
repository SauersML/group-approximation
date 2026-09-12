---
rg: 2
id: fpbs-kazhdan-gradient-via-power-p-deficiency
kind: route
title: Take the residual pro-p image of a Kazhdan group of positive power p-deficiency
target: fpbs-kazhdan-positive-rank-gradient
requires:
  - fpbs-kazhdan-power-p-deficiency-presentation
  - fpbs-power-p-deficiency-schreier-bound
artifacts:
  - research/artifacts/fpbs/docs/power-p-deficiency-excludes-t-2026-09-11.md
---

**Dead: the required premise is refuted.** The implication itself is valid.

Suppose `Gamma` is Kazhdan with `def_p(Gamma) = c > 0`, and let `Gamma'` be its
image in the pro-`p` completion.
- `Gamma'` is infinite and residually `p`, and it is Kazhdan as a quotient.
- The derived `p`-series `D_i(Gamma')` is a normal chain with trivial
  intersection, so it is Farber.
- The kernel lies in every `D_(i+1)(Gamma)`, so
  `d_p(D_i(Gamma')) = d_p(D_i(Gamma))`.
- The Schlage-Puchta inequality then gives
  `(d(D_i)-1)/[Gamma':D_i] >= c`, a positive rank gradient.

`fpbs-power-p-deficiency-excludes-property-t` refutes the premise. What
survives for the target is a residually-`p` Kazhdan group with linear mod-`p`
homology growth along some `p`-chain, from a source other than power
deficiency. The artifact explains why the truncation argument says nothing
there.
