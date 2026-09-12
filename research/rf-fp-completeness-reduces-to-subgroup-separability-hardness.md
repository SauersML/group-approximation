---
rg: 2
id: rf-fp-completeness-reduces-to-subgroup-separability-hardness
kind: claim
title: Residual finiteness of finite presentations is Pi-zero-two complete as soon as separability of finitely generated subgroups of a product of two free groups is Pi-zero-two hard
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  centralizing-hnn-is-residually-finite-iff-edge-is-separable: that is the criterion; this is the complexity-theoretic consequence, which turns one open cell of the ledger into a question of geometric group theory about one fixed ambient group.
  enumerated-subgroup-separability-is-pi3-complete: that concerns enumerated subgroups of a free group, where separability is Pi-zero-three complete; this concerns finitely generated subgroups of a product of two free groups, where the upper bound drops to Pi-zero-two and only hardness is missing.
  finite-presentation-rice-criterion-via-the-fixed-positive-rope: that explains why the compiler route is unavailable for residual finiteness; this supplies the alternative route and names its single missing input.
---

ESTABLISHED (as a reduction).  Let `K = F x F` be a product of two free
groups of rank two and, for a finite tuple `w` of elements of `K`, write
`L_w = <w>` and

```text
Gamma_w = < K, v | [v, w_1] = 1, ..., [v, w_n] = 1 >.                 (RS1)
```

Then `Gamma_w` is **finitely presented**, computably in `w`, and by
[[centralizing-hnn-is-residually-finite-iff-edge-is-separable]]

```text
Gamma_w is residually finite   iff   L_w is separable in K.           (RS2)
```

Consequently

```text
{ w : L_w is separable in F x F }  is Pi^0_2-hard
   ==>  RF_fp is Pi^0_2-complete,                                     (RS3)
```

since `RF_fp` is `Pi^0_2` ([[residual-finiteness-of-enumerated-presentations-is-pi3-complete]],
finite-presentation clause, machine-checked as
`RFPresentationPi02.pi02_residuallyFinite`).

**Why this is the right reduction to attempt.**  The separability index
set is itself `Pi^0_2`: for a finitely generated `L <= K` with `K`
finitely presented and residually finite, separability says that for every
word `k` either `k in L` (recursively enumerable, since `L` is finitely
generated) or some finite quotient of `K` separates `k` from the image of
`L` (also recursively enumerable).  So (RS3) asks for hardness of a
`Pi^0_2` set, not for a new upper bound, and it lives entirely inside the
best-understood non-subgroup-separable group.  Products of free groups are
exactly where separability fails --- Mikhailova subgroups are finitely
generated and non-separable, since separability of a finitely generated
subgroup makes membership decidable --- so the raw material for a
reduction is present; what is missing is a *uniform family* whose
separability tracks an arbitrary `Pi^0_2` event.

## Attempts

The Mikhailova family alone does not suffice: separability of `M(H)`
implies decidability of the word problem of `H`, a `Sigma^0_3`-complete
condition on `H`, so the naive parametrisation by `H` cannot be a
reduction from a `Pi^0_2`-complete set --- the fibres are the wrong shape.
A workable family should vary a finitely generated subgroup continuously
in a `Pi^0_2` parameter, for instance by adjoining to a fixed
non-separable subgroup elements that are switched on at stages, so that
separability is regained exactly when the switching stops.
