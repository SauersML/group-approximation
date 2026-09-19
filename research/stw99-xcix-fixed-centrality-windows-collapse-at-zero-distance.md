---
rg: 2
id: stw99-xcix-fixed-centrality-windows-collapse-at-zero-distance
kind: claim
title: Every fixed centrality window collapses along vanishing-distance XCIX pairs
artifacts:
  - research/artifacts/stw99-xcix-quantitative-audit-2026-08-30.md
---

Fix a dense sequence `(z_j)` in the unit ball of `Z`, with `z_1=1_Z`.  For
a unital C*-algebra `B` and integers `m,k>=1`, set

```text
Delta_(m,k)(B)
 = sup_(x_1,...,x_m in B_1)
     inf_(unital embeddings psi:Z->B)
       max_(i<=m,j<=k) ||[psi(z_j),x_i]||.
```

If `A,B` are unital separable C*-subalgebras with a common unit,
`A` is Z-stable, and

```text
d_KK(A,B)<gamma<1/12600000,
```

then, for every `m,k`,

```text
Delta_(m,k)(B) <= 304 sqrt(gamma)+2 gamma.       (CW)
```

Consequently, for any vanishing-distance sequence of unital XCIX
counterexamples, `Delta_(m,k)(B_n)->0` for every fixed pair `(m,k)`.  Any
failure of Z-stability must escape through increasing finite-set complexity
or decreasing tolerance; no fixed-size, fixed-Z-window obstruction survives.
