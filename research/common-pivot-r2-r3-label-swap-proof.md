---
rg: 2
id: common-pivot-r2-r3-label-swap-proof
kind: route
title: Extend the A6 permutation gauge by equivariant transport arms and binary children
target: common-pivot-r2-r3-data-preserve-a6-label-swap
requires: []
---

Conjugation by `r=(p q)` sends the transposition `(i p)` to `(i q)`,
proving `(CPA2)`.  Direct multiplication gives `t_i s_i=(i p q)`.  For
`i!=j`, `c_i c_j` is a product of two disjoint transpositions, so every
within-chart pair product and the nonshared pair `c_3c_4` have order two.
The permutation of the abstract labels `1,2` fixes `p,q` and therefore fixes
`r`, while interchanging the entire arm pairs `(s_1,t_1)` and `(s_2,t_2)`.
Thus it is an automorphism of all the enriched local data.

The normalized-HS calculation for `(CPA4)` is the one in
`bare-r5-a6-collision-label-swap-countermodel`: `c_1^*c_2` is a three-cycle,
so it has three fixed points on `Omega` and character `3-1=2` on the
five-dimensional standard summand.  Therefore

```text
||c_1-c_2||_2^2=2-2(2/5)=6/5.
```

Diagonal lifting is a homomorphism from `S(Omega)` to the symmetric group on
`Omega times {0,1}`.  It therefore preserves all cube and pair-square
relations.  Equation `(CPA6)` is literal, and its two factors are disjoint
transpositions.  The lift of `c_1^*c_2` is two disjoint three-cycles, hence
has six fixed points on twelve letters.  Its character on the
eleven-dimensional standard summand is `6-1=5`, giving

```text
||hat(c_1)-hat(c_2)||_2^2=2-2(5/11)=12/11.
```

Both defects are exactly zero while the mismatch is positive, proving the
claimed firewall.

