---
rg: 2
id: lin-near-synchrony-selects-one-state-corner
kind: claim
title: Near-synchrony rounding selects one state-dependent corner with relative row control
artifacts:
  - research/artifacts/lin-tracial-rounding-state-gh-source-audit-2026-08-23.md
---

For a `delta`-synchronous tracially embeddable correlation with density
`sigma`, Lin's synchronous rounding supplies spectral corners `P_lambda` for
which

```text
integral tau(P_lambda) d lambda = tau(sigma^2)=1,
integral e_lambda d lambda <= O(delta^(1/4)+delta),
```

where `e_lambda` is the averaged squared row discrepancy on `P_lambda`.
Consequently some `lambda` with `tau(P_lambda)>0` satisfies

```text
e_lambda/tau(P_lambda) <= O(delta^(1/4)+delta).
```

This is a genuine common corner for one state.  It has no uniform trace
floor and is selected from `sigma`, rather than by a fixed group word.  It
therefore cannot by itself supply the common marked source in `(CPS2)` or
align corners arising from different context densities.
