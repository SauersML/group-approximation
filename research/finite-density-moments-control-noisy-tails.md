---
rg: 2
id: finite-density-moments-control-noisy-tails
kind: claim
title: A finite density moment controls high-degree energy after fixed product noise
distinct_from:
  noise-test-sound-on-smooth-design-rich-inputs: that transfers BKM under pointwise density domination; this proves a dimension-free tail estimate using one finite Lq density norm and the existing noise.
artifacts:
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
---

For every integer `m>=2` and `0<rho<1`, there is an integer `q=q(m,rho)>=2`
such that in every dimension `N`, for every probability law `nu` on `[m]^N`,
every subset `E`, real function `F`, and integer `d>=0`,

```
E_nu[1_E |(T_rho F)^(>d)|^2]
 <= ||1_E dnu/dU_N||_q rho^(d+1) ||F||_2^2.
```

All norms on the right use uniform probability measure. The noise keeps
each coordinate with probability `rho` and otherwise resamples it uniformly.
Degree counts nonconstant product factors. The finite exponent is chosen
before the dimension, density bound and degree cutoff. This estimate is
used by `ugc-from-finite-moment-pairing-hardness` to replace the pointwise
domination step in the existing analytic transfer.
