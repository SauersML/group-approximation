---
rg: 2
id: atlas-first-disjoint-mixed-pair-has-zero-reservoir-rank
kind: claim
title: The first distinct-source mixed Atlas pair has zero reservoir-authentication rank
invalidates:
  - atlas-first-disjoint-mixed-pair-authenticates-prefix-reservoir
distinct_from:
  atlas-first-two-mixed-rows-have-zero-reservoir-rank: that treats two rows in the initial same-source root block; this removes that degeneracy and treats the first pair with distinct source columns and target rows.
  atlas-first-nonscalar-mixed-row-is-same-source-commutation: that uses a common source-column annihilation; this uses fully disjoint root indices.
  atlas-mixed-minor-needs-nuisance-quotient-rank: that states the general coefficient criterion; this supplies a nonzero rectangular kernel direction for the first distinct-source candidate.
artifacts:
  - experiments/atlas_first_nonscalar_mixed_row_audit.py
---

**ESTABLISHED EXACT DISTINCT-SOURCE COUNTERMODEL.** Scan the canonical
full-family packet for `orth_ij_kl_rs` subject to

```text
(i<j)!=(k<l),       r,s!=1,       i!=k,       j!=l.   (FDR1)
```

The last two conditions require different target rows and different source
columns, excluding the same-source annihilation used for entries `281,282`.
The first two survivors are zero-based full-family entries `380,381`, hence
packet entries `381,382`:

```text
r_0=[x_12(e),x_43(e)],       r_1=[x_12(e),x_43(f)].   (FDR2)
```

Their translated words have respectively `36,36` syllables and Atlas
`X`-lengths `130,154`. The attached MSI audit reconstructs the canonical
ordering and verifies these data.

Despite the distinct sources, the pair is still rectangularly vacuous. Let
`V_1,...,V_4` be arbitrary finite-dimensional `F_2`-spaces and choose

```text
a:V_2->V_1,           b_0,b_1:V_3->V_4.
```

On their direct sum put

```text
X=1+iota_1 a p_2,     Y_j=1+iota_4 b_j p_3.          (FDR3)
```

Now

```text
(iota_1 a p_2)(iota_4 b_j p_3)=0
=(iota_4 b_j p_3)(iota_1 a p_2)                      (FDR4)
```

because `p_2 iota_4=0` and `p_3 iota_1=0`. Thus both relators in
`(FDR2)` vanish identically while `b_0,b_1` retain arbitrary rank, range,
kernel, and relative gauge. This is not the same-source mechanism: the
blocks are supported on four distinct root-index incidences.

Choose any nonzero desired mismatch in the free pair `(b_0,b_1)`. Every
compressed residual derived from `(FDR2)` is zero, so the converse direction
of `atlas-mixed-minor-needs-nuisance-quotient-rank` again puts the desired
column in the nuisance span. The nuisance-quotient rank increment is zero.
The finite left regular representation supplies an exact unitary model, and
substituting coherent prefix-window maps for `a,b_j` preserves `(FDR4)`.

Therefore merely leaving the common-source block does not find the Atlas
authenticator. The next minimal candidate must include a composable
multiplication triangle or a return word, not only St2 orthogonality rows.

DERIVATION
atlas-first-disjoint-mixed-pair-zero-rank-proof
