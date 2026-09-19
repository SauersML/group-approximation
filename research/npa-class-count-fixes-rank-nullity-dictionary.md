---
rg: 2
id: npa-class-count-fixes-rank-nullity-dictionary
kind: claim
title: The class count turns the dimension law into a rank increment of five k minus one
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

With `C_k = (5k+2)(k+1)/2` the number of moment classes at level `k`, and
`Phi_k` regarded as the linear map `y |-> N_k^T Gamma_k(y) N_k` on `R^(C_k)`,
the following four statements are equivalent for a fixed `k >= 3`, given the
corresponding statement at `k-1`:

```text
(N)  dim ker Phi_k        = 2k+3
(R)  rank Phi_k           = (5k^2 + 3k - 4)/2
(I)  rank Phi_k - rank Phi_(k-1)   = 5k - 1
(S)  dim ker Phi_k - dim ker Phi_(k-1) = 2
```

The arithmetic behind them: `C_k - C_(k-1) = 5k+1`, so exactly `5k+1` moment
classes are new at level `k` -- precisely the classes of total degree `2k-1` and
`2k`; and `C_k - (2k+3) = (5k^2+3k-4)/2`.  Base values are `C_2 = 18`,
`C_3 = 34`, and the claimed nullities `dim ker Phi_2 = 7`, `dim ker Phi_3 = 9`
correspond to `rank Phi_2 = 11`, `rank Phi_3 = 25`.

Consequently the shell bookkeeping `5k+1 = (5k-3) + 4` with two old gauge
freedoms consumed is not an independent fact but a restatement of `(S)`: four
fresh high-degree freedoms minus two consumed old ones is the `+2` per level.
Any argument delivering the rank increment `5k-1` delivers the dimension law,
and conversely.

This node exists so that later nodes may quote whichever of the four forms is
convenient without re-deriving the conversion, and so that the shell narrative
is on record as bookkeeping rather than as evidence.
