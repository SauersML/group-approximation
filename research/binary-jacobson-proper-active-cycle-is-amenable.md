---
rg: 2
id: binary-jacobson-proper-active-cycle-is-amenable
kind: claim
title: Every proper part of the active constant three-cycle is an amenable marked Jacobson subsystem
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
distinct_from:
  binary-jacobson-active-cycle-generates-rank-three: that proves the complete directed three-cycle with one balanced shift generates the full rank-three elementary core; this proves that deleting any one cycle edge restores an amenable marked subsystem, even after adjoining the whole finitary kernel.
  binary-jacobson-monomial-symbol-preimage-is-marked-mf: that treats the preimage of monomial Laurent symbols; this allows one or two nonmonomial constant root symbols, using acyclicity to place them in a solvable Laurent triangular group.
  binary-jacobson-two-target-parabolic-is-marked-mf: that places raw roots in external target columns; this establishes the sharp minimal threshold for raw roots on the active directed cycle itself.
---

**ESTABLISHED.**  Put

```text
J=F_2<S,T | TS=1>,       Q=1-ST,
E=EL_5(J),               L=ker(E -> EL_5(F_2[z,z^(-1)])).
```

Let `a_12` be the balanced shift on active rows `1,2`, and let `D` be a
proper subset of the directed constant cycle

```text
{x_12(1),x_23(1),x_31(1)}.                             (JMIN1)
```

Then

```text
H_D=<L,a_12,D>                                          (JMIN2)
```

is amenable.  It contains the nontrivial head root `x_13(Q) in L`, so it is
operator-MF with that mark visible.

Together with `binary-jacobson-active-cycle-generates-rank-three`, this is a
sharp minimality statement for the directed-cycle family.  One balanced
shift and zero, one, or two of the three raw cycle edges admit a faithful
marked MF model.  Adding the third edge is the first unfenced package, and
it immediately generates `EL_3(J)`.  Hence no smaller subcycle supplies an
oriented Hall deficit, while the complete subcycle is already the hard
rank-three coefficient core rather than a finite type-counting gadget.

DERIVATION
binary-jacobson-proper-cycle-amenability-proof
