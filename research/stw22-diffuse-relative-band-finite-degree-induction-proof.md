---
rg: 2
id: stw22-diffuse-relative-band-finite-degree-induction-proof
kind: route
title: Apply degree-d Michael selection to every dyadic band over B^(d+1)
target: stw22-diffuse-relative-low-spectrum-all-finite-balls
requires:
  - stw22-diffuse-stiefel-all-finite-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-five-ball-extension
artifacts:
  - research/artifacts/stw22-diffuse-all-degree-induction-audit-2026-08-31.md
---

Fix a finite `d`. Split the nonzero low weight into bounded dyadic spectral
bands. After extending earlier bands, the moving complement retains the
strict trace reserve

```text
tau(e)-tau(p_h)-sum_(k<=n)tau(r_k)>=delta_0>0.         (AD-3)
```

For the next band use the full moving-corner Stiefel value in the interior
and the prescribed singleton on `S^d`. The two-neighbourhood relative
argument proves lower semicontinuity. Full values are isometric to
Stiefel spaces in diffuse corners of trace at least `delta_0`.

The all-finite-degree Stiefel theorem supplies `d`-connectivity and common
`LC^0` through `LC^d` moduli. Michael with index `d` selects the band over
`B^(d+1)` with exact boundary. Iterate. Orthogonal weighted tails converge
uniformly in `2`-norm, product relations pass to `L^1`, and the fibre
diameter gives the quantitative bound. This argument is performed
separately for each finite `d`; no infinite-dimensional Michael theorem is
invoked.