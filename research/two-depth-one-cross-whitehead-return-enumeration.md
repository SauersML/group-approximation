---
rg: 2
id: two-depth-one-cross-whitehead-return-enumeration
kind: route
title: Prefilter two distinct nonnormal root channels and check every signed Hecke generator
target: two-depth-one-nonnormal-roots-do-not-return-cross-whitehead
requires:
  - one-depth-one-occurrence-does-not-return-cross-whitehead
  - two-depth-one-leavitt-roots-return-only-constantly
---

Enumerate the `336` depth-one roots and apply the exact ten-generator signed
normalizer test to each one.  Removing the `32` roots in the four known
nonconstant-normalizer positions leaves `304` roots in `38` positions.
Form all ordered pairs whose positions differ, proving `(TDR3)`.

For a source candidate put `g=LK_i`; for a native-target candidate put
`g=J_1^(-1)LK_i`.  First test

```text
g^(-1)x_28(1)g in L_0
```

with the correct character sign.  The exact prefix normal form leaves only
the two source words `(TDR4)` and no native-target word.  Direct word
cancellation proves `(TDR5)`.  Testing the remaining nine signed generators
rejects both source survivors.

The MSI artifact asserts `304` roots, `38` positions, `89984` pairs per
case, and `359936` total tests.  It also asserts the exposed-row counts
`(1,0,1,0)` and the full-signature counts `(0,0,0,0)` in the order
`(K_0->Q,K_0->J_1Q,K_1->Q,K_1->J_1Q)`.  This completes the scoped exact
enumeration.
