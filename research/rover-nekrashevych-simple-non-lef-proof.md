---
rg: 2
id: rover-nekrashevych-simple-non-lef-proof
kind: route
title: Restrict trivial states to the Higman--Thompson subgroup and then take commutators
target: rover-nekrashevych-simple-groups-are-not-lef-or-torsion-free
requires: []
---

In arXiv:2510.01952, Definition 2.2 and the paragraph following it identify

```text
V_d=V_d({1}) <= V_d(H)
```

as the subgroup represented by diagrams with trivial `H`-labels.
Proposition 2.3(2) records simplicity of the relevant commutator subgroups.
Functoriality of commutators gives

```text
V_d'=[V_d,V_d] <= [V_d(H),V_d(H)]=S.                  (RNS2)
```

The Higman--Thompson group `V_d` is of type `F_infinity`; its commutator is
therefore finitely presented (it has finite index), infinite and simple.  An
infinite finitely presented simple group is not LEF: finite presentation
would upgrade LEF to residual finiteness, while an infinite simple residually
finite group would embed in a nontrivial finite quotient and hence be finite.
Since subgroups of LEF groups are LEF, `(RNS2)` proves that `S` is not LEF.

Finally `V_d'` contains nontrivial even permutations of the leaves of a
sufficiently expanded finite `d`-ary tree, for example a 3-cycle.  These have
finite order in `V_d'`, hence also in `S`.  This proves both clauses of
`(RNS1)`.  End proof.
