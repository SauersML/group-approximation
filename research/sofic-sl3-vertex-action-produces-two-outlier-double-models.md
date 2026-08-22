---
rg: 2
id: sofic-sl3-vertex-action-produces-two-outlier-double-models
kind: claim
title: Soficity of the SL3 building vertex action produces canonical double microstates with both vertices uniformly uncorrectable
distinct_from:
  sl3-regular-double-collapse-forces-nonsofic-vertex-action: that uses the fold word to refute regular fold collapse conditionally; this targets the smaller correctable-vertex terminal and proves the resulting models lie in the simultaneous two-outlier sector.
  sl3-double-one-near-vertex-forces-joint-near-exactness: that excludes a mixed near/far enemy abstractly; this supplies a conditional source of enemies and proves neither vertex can be near exact.
---

Let `X=A/C` for

```text
A=SL_3(Z[1/2]),       C=SL_3(Z).
```

If the action `A action X` is sofic, then there are canonical-character
permutation microstates `sigma_n` of `D=A*_C A` and a constant
`epsilon_0>0` such that, for both vertex restrictions,

```text
inf_(alpha:A->U(d_n) exact)
 max_(s in S_A)||pi_(n,j)(s)-alpha(s)||_2 >= epsilon_0,
 j=0,1,                                                       (SOM1)
```

along a subsequence.  Consequently soficity of the building vertex action
refutes `sl3-canonical-double-has-a-correctable-vertex` directly, not merely
the downstream fold collapse.  Conversely, establishing that correctable-
vertex terminal would prove this explicit action nonsofic.

