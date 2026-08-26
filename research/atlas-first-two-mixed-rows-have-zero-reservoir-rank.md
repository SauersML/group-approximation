---
rg: 2
id: atlas-first-two-mixed-rows-have-zero-reservoir-rank
kind: claim
title: The first coupled mixed Atlas pair has zero reservoir-authentication rank
invalidates:
  - atlas-first-two-mixed-rows-authenticate-prefix-reservoir
distinct_from:
  atlas-first-nonscalar-mixed-row-is-same-source-commutation: that kills packet entry 281 by itself; this treats the first coupled family, retaining its shared coarse occurrence and both fine coefficient branches.
  atlas-mixed-minor-needs-nuisance-quotient-rank: that gives the exact general rank criterion after a typed coefficient matrix exists; this proves that the first two-row candidate has an exact rectangular kernel direction and hence cannot pass any such criterion.
  mixed-steinberg-loops-admit-morita-rectangular-model: that handles arbitrary pasted Steinberg diagrams categorically; this identifies the canonical first two-row family and the particular shared-occurrence escape.
artifacts:
  - experiments/atlas_first_nonscalar_mixed_row_audit.py
---

**ESTABLISHED EXACT COUPLED-ROW COUNTERMODEL.** In the canonical packet
ordering, the first two mixed-direction rows with no displayed constant
coefficient are zero-based full-family entries `280,281`, hence packet
entries `281,282`:

```text
r_0=[x_12(e),x_32(e)],       r_1=[x_12(e),x_32(f)].    (FTR1)
```

Both translated two-chart words have `52` syllables; their Atlas `X`-lengths
are respectively `166` and `226`. The attached sparse MSI replay verifies
the ordering and word sizes.

The common occurrence in `(FTR1)` does not authenticate a common reservoir.
Let `V_1,V_2,V_3` be arbitrary finite-dimensional `F_2`-spaces and choose

```text
a:V_2->V_1,       b_0,b_1:V_2->V_3
```

arbitrarily. Put

```text
X=1+iota_1 a p_2,       Y_j=1+iota_3 b_j p_2.         (FTR2)
```

For both `j=0,1`,

```text
(iota_1 a p_2)(iota_3 b_j p_2)=0
=(iota_3 b_j p_2)(iota_1 a p_2),                      (FTR3)
```

so `[X,Y_0]=[X,Y_1]=1` exactly. The maps `b_0,b_1` remain completely
arbitrary; in particular their ranks, kernels, ranges, and relative gauge
may be chosen independently. Taking the finite left regular representation
again gives an exact unitary permutation model.

This also computes the relevant nuisance-quotient obstruction without
inventing a typed census. Any proposed compressed coefficient system derived
only from `(FTR1)` has zero residual on every choice of `b_0,b_1`. Choose a
nonzero desired coarse/fine mismatch in that free pair. Then the residual
vector is zero while the desired vector is nonzero, so the converse
`(AMQ10)` of `atlas-mixed-minor-needs-nuisance-quotient-rank` applies: the
desired column lies in the nuisance span and the quotient-rank increment is
zero, not one (and certainly not three).

In a coherent prefix window, substitute the actual truncated `e` and `f`
coefficient maps for `b_0,b_1`. Equation `(FTR3)` still makes both packet
rows exact. Thus the first minimal coupled family after entry 281 does not
damage the ultra-deep tower. A viable family must leave this same-source
orthogonality block and include a mixed multiplication/return whose joint
typing cannot be realized in the rectangular category.

DERIVATION
atlas-first-two-mixed-rows-zero-rank-proof
