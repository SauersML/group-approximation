---
rg: 2
id: tracial-bcs-has-rational-balanced-hyperoctahedral-atlas
kind: claim
title: Every tracial finite BCS has a rational rank-balanced hyperoctahedral context atlas
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that gives equal repetition separately in every context and need not balance a shared variable's two eigenspace ranks; this uses tracial feasibility only to choose rational atom multiplicities whose shared binary marginals match exactly.
  oracularizable-tracial-nonru-game-exists: that converts games while preserving a non-RU trace; this extracts a finite rational local-marginal point and makes no claim that the resulting context blocks form a global BCS representation.
---

Let `B` be a finite BCS whose algebra has a tracial state.  There are a
positive integer `D`, nonnegative integers

```text
n_(c,a),       a in R_c,        sum_(a in R_c)n_(c,a)=D,  (RBH1)
```

and, for every shared variable `x in U_c intersect U_d`, a permutation
`pi_(c,d,x) in S_D`, with the following properties.

Label the coordinates of `C^D` in context `c` by `n_(c,a)` copies of every
allowed assignment `a`.  Let

```text
d_(c,x) delta_(a,j)=a_x delta_(a,j).                     (RBH2)
```

Then

```text
pi_(c,d,x) d_(c,x) pi_(c,d,x)^(-1)=d_(d,x).              (RBH3)
```

All context packets may therefore use copies of the same hyperoctahedral
group `K_D=(C_2)^D semidirect S_D`, the same tautological irreducible type,
and the same signed corner `q_D`.  The assignment atom `a` has rank
`n_(c,a)`, and every shared binary marginal has exactly the same pair of
integer ranks at both endpoints.

The integers and permutations are effectively computable from the finite
BCS alone once feasibility is known: solve the rational local-marginal
polytope, clear denominators, and match the two sign fibers.  This does not
give a finite-dimensional BCS representation.  The permutations in `(RBH3)`
are chosen separately for incidences and need not have coherent product
around cycles.
