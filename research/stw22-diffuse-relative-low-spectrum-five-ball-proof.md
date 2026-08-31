---
rg: 2
id: stw22-diffuse-relative-low-spectrum-five-ball-proof
kind: route
title: Run the relative dyadic-band recursion with degree-four Stiefel values
target: stw22-diffuse-relative-low-spectrum-five-ball-extension
requires:
  - stw22-diffuse-stiefel-uniform-four-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-four-ball-extension
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

Use the dyadic spectral bands `r_n` of `b` from the lower-degree relative
proof. If `b=0`, take `X=0`. Otherwise, after extending the preceding
band frames, the moving complement

```text
g_n=f-sum_(k<n)V_kV_k^*
```

satisfies the unchanged reserve

```text
tau(g_n)-tau(r_n)
 =tau(e)-tau(p_h)-sum_(k<=n)tau(r_k)>=delta_0>0. (R5-3)
```

Use the full interior value `{v:v^*v=r_n,vv^*<=g_n}` and the prescribed
singleton boundary frame on `S^4`. The same two-neighbourhood argument
proves lower semicontinuity at the boundary; no collar is assumed.

Each full value is isometric, through an arbitrary reference frame, to a
Stiefel space in the diffuse corner `g_nNg_n`. The degree-zero through
degree-four theorems give common `LC^0`--`LC^4` moduli and global
four-connectivity after normalized-corner scaling. Michael with `n=4`
therefore selects each band over `B^5` with exact boundary.

The weighted sums `sum_n V_nb^(1/2)r_n` converge uniformly because the
squared tail is `sum tau(br_n)`. Operator-ball closedness, `L^1` product
passage, and exact boundary recovery are identical to the four-ball proof.
The fibre diameter gives (R5-2).