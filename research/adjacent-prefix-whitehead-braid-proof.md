---
rg: 2
id: adjacent-prefix-whitehead-braid-proof
kind: route
title: Regard the nested partial Whitehead words as three submodule transpositions
target: adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
---

Put `e_m=s_(0^m)t_(0^m)`.  On the three external coordinates
`k_1,k_2,k_3`, the word `W_1` exchanges

```text
e_1 R at k_1    with    e_2 R at k_2
```

through the inverse pair `c_1,d_1`, and fixes both complementary summands.
Likewise `W_2` exchanges

```text
e_2 R at k_2    with    e_3 R at k_3
```

through `c_2,d_2`.  These are the adjacent transpositions of three disjoint
isomorphic summands.  Direct block multiplication, using

```text
c_md_m=e_(m+1),       d_mc_m=e_m,
```

therefore gives the two involution identities and the Coxeter braid in
`(APB1)`.  The same calculation may be expanded into ordinary spare-index
Steinberg commutators; no opposite-root commutator formula is needed for
the conjugation action.

Insert `(APB2)` into `(APB1)`.  The fixed tensor-factor swaps are
involutions and themselves satisfy

```text
SWAP_(1,2)SWAP_(2,3)SWAP_(1,2)
 =SWAP_(2,3)SWAP_(1,2)SWAP_(2,3).
```

Cancel this common label factor.  The square relations give `V_m^2=1`, and
the braid gives `(APB3)`.  Finally, for involutions satisfying the braid,

```text
(V_1V_2)V_1(V_1V_2)^(-1)
 =V_1V_2V_1V_2V_1
 =V_2,
```

where the middle equality uses `(APB3)` and `V_m^2=1`.  This proves
`(APB4)`.
