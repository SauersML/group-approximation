---
rg: 2
id: s4-standard-corner-realizes-shared-nand-chord-proof
kind: route
title: Use the S3 branching of the standard S4 representation and complementary transpositions
target: s4-standard-corner-realizes-shared-nand-chord
requires: []
---

The standard representation of `S_4` is irreducible of dimension three,
which gives `(SNC1)`.  Restricted to the point stabilizer `S_3`, the
four-point permutation representation decomposes as

```text
1_(S_4)|_(S_3) direct_sum rho|_(S_3)
 =2*1_(S_3) direct_sum std_(S_3).
```

Cancelling one trivial summand proves `(SNC3)`.  Since `q` is central in
`C[S_4]`, it commutes with `e_std`; hence `p=qe_std` is a projection, and
the branching formula gives its ranks.

Fix a transposition `s in H`.  On the trivial summand of `(SNC3)`, `s` has
sign `+`; on `std_H`, a transposition has one `+` and one `-` eigenline.
The projection `p` is one on the standard summand and zero on the trivial
summand.  This gives exactly the four ranks in `(SNC6)`.

The complementary transposition `u_s` is disjoint from `s`, so they commute.
Centrality of `q` gives `[qu_s,qs]=0`.  Conjugating `(SNC4)` by `qu_s`
gives `p`, hence conjugates `Y_s` to `Z`; conjugating the commutation
relation `[S_s,Z]=0` back by the same separator-fixing unitary gives
`[S_s,Y_s]=0`.  This proves `(SNC5)`.

The rank statement `(SNC6)` is the truth table with only `(-,-)` forbidden,
and division by the separator-atom ranks gives `(SNC7)`.  Finally each of the
three transpositions in the point stabilizer has the displayed disjoint
complementary transposition, proving the three-context incidence-star
statement entirely inside the same finite `S_4` corner.
