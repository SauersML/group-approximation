---
rg: 2
id: intermediate-fold-arm-has-finite-s6-model
kind: claim
title: The authenticated intermediate fold arm has a finite S6 model
artifacts:
  - research/intermediate-fold-arm-s6-proof.md
distinct_from:
  two-step-fold-loop-has-finite-64-model: that checks only the final nested return and realizes it as a mixed second difference; this names the intermediate root and requires an involutory transport from the original coefficient-arm occurrence to that intermediate occurrence.
  one-arm-range-sum-whitehead-has-marked-model: that authenticates a Pauli arm inside inverse and reverse output rows while leaving its complementary controlled arm movable; this authenticates the new root created after the range fold is multiplied by the shared arm.
---

**ESTABLISHED INTERMEDIATE-OCCURRENCE COUNTERMODEL.**  Strengthen the
two-step fold cell by naming the first propagated root `E` and requiring

```text
C_0C_1=J,
[C_0,S]=E,               [C_1,S]=1,       [J,S]=E,     (IFA1)
[T,E]=M,                 [S,T]=1.                       (IFA2)
```

Here every `S` is the same individual `s_u` arm occurrence and every `T` is
the same individual `t_u` arm occurrence.  Authenticate `E` as a transported
occurrence of that very coefficient arm by adjoining one root-position
transport `W` with

```text
W^2=1,                   WSW^(-1)=E.                   (IFA3)
```

All named root occurrences are involutions.  The row `(IFA3)` rules out the
order-64 square-zero model in `two-step-fold-loop-has-finite-64-model`: there
`S` has nontrivial image in the actor quotient, while `E=[C_0,S]` lies in the
normal additive kernel, so the two cannot be conjugate.

Nevertheless `(IFA1)--(IFA3)` have an exact marked finite model.  In `S_6`
use

```text
S  =(3 4)(5 6),             T=(5 6),
C_0=(1 2)(4 5),             C_1=(3 6)(4 5),
J  =(1 2)(3 6),             E=(3 6)(4 5),
W  =(4 6),                  M=(3 4)(5 6).              (IFA4)
```

Direct permutation multiplication proves all the rows, including the
literal occurrence transport, while `M!=1`.  Thus naming and conjugately
authenticating only the first propagated arm does not imply `(BAC1)`.  The
new finite escape is not affine linear: it lets `C_0,S,C_1` form overlapping
Klein-four patterns on different four-point supports, and the final arm `T`
reads their overlap.

A successful next cell must couple the transport `W` to the **prescribed
Whitehead factorization and its other shared occurrences**, or authenticate
the second arm at the final multiplication as well.  An abstract involutory
root-position conjugacy of the intermediate coefficient is insufficient.

This is a scoped obstruction to the displayed occurrence table, not a model
of the full signed Leavitt/Whitehead presentation.  No Property `(T)`,
Kazhdan input, stability theorem, trace hypothesis, or literature result is
used.

DERIVATION
intermediate-fold-arm-s6-proof

