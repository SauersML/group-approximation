---
rg: 2
id: locally-free-groups-first-l2-betti-equals-c-star-minus-one
kind: claim
title: A countable locally free group has first L2-Betti number equal to its eventual minimal subgroup rank minus one
distinct_from:
  l2-normal-rank-bound-fails-for-torsion-free-groups: that imports Fisher--Lodha's computation beta_1 = n for one specific family of locally free groups; this computes beta_1 for every countable locally free group, as c* - 1.
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

**ESTABLISHED** through `locally-free-groups-first-l2-betti-equals-c-star-minus-one-proof`.

Let `Γ` be a countably infinite locally free group, meaning every finitely
generated subgroup is free. For finite `F ⊆ Γ` put

```text
c_F(Γ) = min { rk L : L ≤ Γ finitely generated, F ⊆ L },     c*(Γ) = sup_F c_F(Γ).
```

Then

```text
beta_1^(2)(Γ) = c*(Γ) − 1      in [0, ∞].
```

For finite `F` containing a nontrivial element, `c_F` is the least fixed price
of a finitely generated subgroup containing `F`, because free groups have
fixed price equal to their rank. So `c*` is the quantity of Theorem G in
`research/artifacts/fpbs/docs/fixed-price-countable-passage.md`.

**Examples.**
- `Γ = F_r`: `c* = r`.
- `Γ = Q`: `c* = 1`.
- Fisher–Lodha's `Γ_n` has `beta_1^(2) = n`, so `c*(Γ_n) = n + 1`.
- `Γ_mal` (`c* = 2`) has `beta_1^(2) = 1`.

**Key point.** A minimal-rank exhaustion `Δ_0 ≤ Δ_1 ≤ ⋯` has every stage
compressed in every later stage. By Jaikin-Zapirain, compressed stages are
`L²`-independent, so the directed colimit loses no `L²`-homology. An arbitrary
exhaustion can lose it: for example, an index-2 rank-3 subgroup of `F_2`.

Artifact: `research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md`, §§2–4.
