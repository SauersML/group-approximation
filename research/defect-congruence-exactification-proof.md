---
rg: 2
id: defect-congruence-exactification-proof
kind: route
title: Descend the permutations and blow quotient classes back up with their original multiplicities
target: defect-congruence-exactifies-permutation-table
requires: []
---

Because `E` is invariant under `sigma_s` and its inverse, `sigma_s` sends each
`E`-class bijectively onto an `E`-class of the same cardinality.  Hence
`(DCE2)` is well defined and bijective on `Y`.

Fix a relation `r=(g,h,k)`.  If an `E`-class `C` meets `G_r`, choose
`i in C cap G_r`.  For any `j in C`, invariance gives

```text
sigma_g sigma_h(j)
 E sigma_g sigma_h(i)
 E sigma_k(i)
 E sigma_k(j),
```

where the middle step is the generating defect pair `(DCE1)`.  Therefore the
relation holds on every copy over `C`.  A quotient class on which the relation
can fail is disjoint from `G_r`, so the total number of copies over all such
classes is at most `|X\G_r|`.  Dividing by `|Y|=|X|` proves `(DCE3)`.

Finally, for any `E`-class `C`, invariance makes the assertion
`sigma_u(i) E sigma_v(i)` independent of the representative `i in C`.
The lifted word maps agree on every copy over `C` exactly in that case.
Weighting the class by its `|C|` copies gives `(DCE4)` after summing over the
classes.