---
rg: 2
id: maslov-finite-subgroup-atlas-no-go-proof
kind: route
title: Scale the compatible projective-regular ray on every finite atlas
target: maslov-finite-subgroup-atlas-no-go
requires: []
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

For a finite subgroup `H`, let `Reg_alpha(H)` denote its `alpha|H`-projective
left-regular representation.  If `K <= H`, then

```text
Res^H_K Reg_alpha(H) = [H:K] Reg_alpha(K).                (FAN1)
```

Indeed, after choosing left `K`-coset representatives, the twisted left action
of `K` preserves each coset summand and every summand is a copy of the twisted
regular module; the cocycle restriction is the same global `alpha|K` on every
chart.

Let `L` be a common multiple of all `|H_i|`.  Put

```text
V_i = (L/|H_i|) Reg_alpha(H_i).                           (FAN2)
```

On an overlap `K_ij`, `(FAN1)` gives

```text
Res V_i = (L/|K_ij|) Reg_alpha(K_ij) = Res V_j.           (FAN3)
```

Thus the multiplicity vectors of the `V_i` form a nonzero rational/integral
ray satisfying every overlap equation exactly.  Any homogeneous cone
inequality that claims positive mismatch for every nonzero `alpha`-sector
multiplicity system is therefore false.

This does not construct a global finite-dimensional `alpha`-projective
representation of `Gamma`: compatibility of finitely many finite subgroup
charts is exactly the information that has been shown insufficient.
