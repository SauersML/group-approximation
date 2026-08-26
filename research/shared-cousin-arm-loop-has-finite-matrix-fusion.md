---
rg: 2
id: shared-cousin-arm-loop-has-finite-matrix-fusion
kind: claim
title: The cross-address loop with literally shared cousin arms has a finite matrix-fusion model
distinct_from:
  depth-two-cousin-loop-has-finite-ut5-fusion-model: that assigns a complete noncommuting payload chain to each character chart and lets S3 permute the chains; this uses one common coefficient matrix algebra, so every inverse, cross-zero, reverse-range, and mixed-loop occurrence is literally the same matrix unit wherever it appears.
  mixed-steinberg-loops-admit-morita-rectangular-model: that keeps the source and doubled target identities distinct; this imposes their group-root equality by one central scalar-root quotient while preserving the marked source root.
  leavitt-range-sum-fold-does-not-pay-reynolds: that separates the fold into an auxiliary UT4 factor; here the fold and all noncommuting payload arms live in one finite matrix-unit group before taking the central quotient.
artifacts:
  - research/shared-cousin-matrix-fusion-proof.md
---

**ESTABLISHED STRONG SHARED-OCCURRENCE COUNTERMODEL.**  Let `u,v` be two
distinct depth-two cousin addresses.  Retain the literal coefficient arms

```text
t_u,s_u,t_v,s_v,
```

all inverse and crossed-zero products, both reverse products, the mixed
four-arm loop

```text
t_u s_u t_v s_v=A,                                    (SCF1)
```

the two partial-Whitehead address moves, and the object-erasing range fold

```text
s_ut_u+s_vt_v=A.                                      (SCF2)
```

Every occurrence is shared: the `t_u` in its diagonal inverse row is the
same coefficient used in `(SCF1)` and in its Whitehead, and similarly for
the other three arms.  Groupify all coefficient products by adjacent-root
Steinberg commutators on a fixed five-root-position chart.

This whole bounded table has an exact finite marked model.  On a
three-dimensional coefficient space with rank-one object projections
`p,q_u,q_v`, use the literal rectangular matrix units

```text
t_i=E_(p,q_i),                  s_i=E_(q_i,p).          (SCF3)
```

Then all inverse, crossed-zero, reverse, and mixed products are exact, while

```text
s_ut_u+s_vt_v=q_u+q_v=1-p.                             (SCF4)
```

In the top central root subgroup of `UT_5(M_3(F_2))`, quotient by the scalar
root `x_15(1)`.  Characteristic two turns `(SCF4)` into

```text
x_15(q_u+q_v)=x_15(p),                                 (SCF5)
```

which is exactly the required fold.  The marked element `x_15(p)` survives
because `p` is not in the scalar line `F_2 1`.  Coefficient-basis
transpositions preserve that scalar line, descend to the quotient, and are
the two finite Whitehead address moves; they conjugate every shared arm and
the marked source corner to its named target occurrence.

Thus even a fixed noncommuting word mixing arms from different addressed
payload copies does not imply `(BAC1)`, when the word stays inside one
finite source/two-target matrix-unit chart and the only same-object return is
the central output fold.  The next relation must propagate the fold
**out of the central output root** into another composable root occurrence.
Equivalently, it must multiply the identified parent/range output by a
shared coefficient arm after the identification; otherwise the scalar-root
quotient absorbs the entire discrepancy.

No Property `(T)`, Kazhdan input, stability theorem, or literature result is
used.

DERIVATION
shared-cousin-matrix-fusion-proof
