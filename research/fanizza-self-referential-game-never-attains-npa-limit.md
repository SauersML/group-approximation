---
rg: 2
id: fanizza-self-referential-game-never-attains-npa-limit
kind: claim
title: An effectively specified BCS game never attains its commuting value at a finite NPA level
artifacts:
  - research/artifacts/fanizza-npa-ingestion-delta-2026-08-20.md
distinct_from:
  kleene-mipco-self-destroying-game: that uses the MIPco compiler to separate commuting and finite-dimensional values; this fixed point has equal NPA limit and commuting value but strict inequality at every finite relaxation level.
  fanizza-et-al-computable-bcs-signal-family: that supplies the parameterized threshold compiler; this diagonalizes that compiler against all finite NPA levels.
---

There is an effectively specified finite BCS game `G_*` and a computable
rational `theta_*` such that

```text
omega_qc(G_*)=theta_*,                                           (FNA1)
omega_npa^(k)(G_*)>theta_*  for every finite k.                  (FNA2)
```

Choose the recursion-theorem machine `M_*` which computes its own threshold
game and halts exactly when the exact semialgebraic decision procedure finds
some `k` with `omega_npa^(k)(G_(M_*))<=theta_(M_*)`.  If it halted, the
membership side of the game compiler would give
`omega_qc>theta`, contradicting that halting test because every NPA value is
an upper bound.  Hence it does not halt.  The nonmembership side gives
`omega_qc<=theta`, while nonhalting gives `(FNA2)`; convergence of the NPA
hierarchy forces equality in `(FNA1)`.

This is an existence-by-effective-self-reference result.  It does not
provide a group presentation or a finite-dimensional-only marked word.
