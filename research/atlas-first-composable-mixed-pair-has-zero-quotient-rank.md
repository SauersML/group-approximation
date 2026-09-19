---
rg: 2
id: atlas-first-composable-mixed-pair-has-zero-quotient-rank
kind: claim
title: The first composable mixed Atlas pair has zero rank modulo its product nuisances
invalidates:
  - atlas-first-composable-mixed-pair-authenticates-prefix-reservoir
distinct_from:
  atlas-first-disjoint-mixed-pair-has-zero-reservoir-rank: that removes the first disjoint St2 pair because both products vanish; this treats the first genuinely composable St3 products and keeps their nonzero right-hand sides.
  mixed-steinberg-loops-admit-morita-rectangular-model: that gives the general categorical escape; this identifies the first canonical composable family and computes its explicit nuisance coefficient matrix.
  atlas-mixed-minor-needs-nuisance-quotient-rank: that supplies the general rank criterion; this evaluates it on the first composable family and obtains rank increment zero.
artifacts:
  - experiments/atlas_first_nonscalar_mixed_row_audit.py
---

**ESTABLISHED EXACT COMPOSABLE COUNTERMODEL.** Scan the canonical
full-family packet for `st3_ijk_rs` with both coefficients nonconstant and
with the three roots `ij,jk,ik` not all having the same orientation. The
first two survivors are zero-based full-family entries `3260,3261`, hence
packet entries `3261,3262`:

```text
r_0=[x_13(e),x_32(e)] x_12(ee)^(-1),
r_1=[x_13(e),x_32(f)] x_12(ef)^(-1).                 (FCM1)
```

Their translated words have `85` syllables each and Atlas `X`-lengths
`271,343`. The attached MSI audit reconstructs the canonical ordering and
checks these values.

Unlike the preceding St2 rows, `(FCM1)` has a nonzero block product. Let
`V_1,V_2,V_3` be arbitrary finite-dimensional `F_2`-spaces and choose

```text
A:V_3->V_1,          B_0,B_1:V_2->V_3
```

arbitrarily. Define

```text
C_j=A B_j:V_2->V_1.                                  (FCM2)
```

The elementary block transvections satisfy exactly

```text
[1+iota_1 A p_3,1+iota_3 B_j p_2]
   =1+iota_1 C_j p_2                                 (FCM3)
```

for both `j`. Thus the two St3 residuals vanish for every `A,B_0,B_1` once
their right-hand-side path products are retained.

This gives the literal nuisance-quotient calculation. If the two desired
columns are the composable products `A B_0,A B_1` and the two nuisance
columns are the right-hand-side occurrences `C_0,C_1`, the coefficient
system is

```text
C=I_2,             D=-I_2.                           (FCM4)
```

Hence

```text
rank[C D]=2=rank(D),                                 (FCM5)
```

so the desired rank increment is zero. Deleting the `C_j` columns would
manufacture rank two, but that is exactly the nuisance-deletion error ruled
out by `atlas-mixed-minor-needs-nuisance-quotient-rank`.

The same construction works at every amplification and in every coherent
prefix window: choose the actual truncated `e,f` maps as `B_j` and interpret
the `ee,ef` paths as their products with `A`. Therefore the first genuinely
composable family adds no same-reservoir control. A viable family must add a
return which identifies at least one product RHS with an already
authenticated occurrence, rather than introducing a fresh product nuisance
for every multiplication row.

DERIVATION
atlas-first-composable-mixed-pair-zero-rank-proof
