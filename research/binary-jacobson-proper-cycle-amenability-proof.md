---
rg: 2
id: binary-jacobson-proper-cycle-amenability-proof
kind: route
title: Topologically order the missing-edge cycle and triangularize its Laurent symbols
target: binary-jacobson-proper-active-cycle-is-amenable
requires:
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
  - amenable-implies-operator-mf
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
---

Under the Laurent symbol map, `a_12` becomes

```text
d=diag(z,z^(-1),1,1,1).                                (JMINP1)
```

The directed graph on `{1,2,3}` whose edges are the roots in `D` is acyclic:
the only directed cycle available in `(JMIN1)` uses all three edges.  Choose
a total ordering of `{1,2,3}` in which every edge of `D` points forward.

Diagonal conjugation preserves every root position and only multiplies its
coefficient by a Laurent monomial.  Consequently the symbol of `H_D` is
contained in

```text
U_D(F_2[z,z^(-1)]) semidirect <d>,                      (JMINP2)
```

where `U_D` is contained in the unitriangular group for the chosen total
ordering.  That unitriangular group is nilpotent, while `<d>` is cyclic.
Thus `(JMINP2)` is solvable and amenable.

The kernel `L` is the finitary general linear group on the countable
Jacobson module, hence locally finite.  The group `H_D` is an extension of
its locally finite normal subgroup `H_D cap L` by the amenable symbol image
just computed.  It is therefore amenable.

Finally `Q` is the nonzero rank-one head idempotent on the standard
unilateral-shift module, so `x_13(Q)` is a nonidentity element of `L<=H_D`.
The prerequisite `amenable-implies-operator-mf` supplies a faithful norm
matrix-corona model and retains this mark.
