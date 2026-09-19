---
rg: 2
id: exact-literal-e-fin-inf-switch
kind: claim
title: A recursive FIN switch has exactly the two values 1 and the literal non-MF group
distinct_from:
  mf-recognition-recursive-presentations-is-second-level-complete: that only needs a surviving free factor on the FIN branch; this computes the entire presented group on both branches.
  mf-safe-finite-presentation-compiler: that asks for an MF-preserving finite-presentation compiler; this is the countably generated recursive input to the torsion-preserving compiler and makes no MF-permanence assertion about that compiler.
---

Fix the literal finitely presented non-MF group

```text
E=<x_1,...,x_r | R_E>.
```

There is a computable map from c.e.-set indices `e` to countably generated
recursive presentations `P_e` such that

```text
|W_e|=infinity  ==>  P_e ~= 1,
|W_e|<infinity  ==>  P_e ~= E.                         (EFS1)
```

## Construction

At stage `j`, introduce a fresh copy `E_j` of the fixed presentation of `E`.
Compare the finite enumerations of `W_e` available at stages `j` and `j+1`.

* If a new distinct number appears, add the relators killing every generator
  of `E_j`.
* If no new number appears, identify the generators of `E_j` and `E_(j+1)`
  coordinatewise.

Together with the relators `R_E` in every copy, this is a uniformly recursive
presentation.  Its incidence graph is the ray on the vertices `j>=0`, with
an edge exactly at a no-event stage.  Each connected component is therefore
a free amalgamation of copies of `E` along identity maps and is isomorphic to
one copy of `E`, unless one of its vertices is killed, in which case the whole
component is trivial.

If events occur infinitely often, every component is a finite interval ending
at an event vertex and is killed.  The whole free product is trivial.  If the
last event occurs at stage `J`, every component before `J` is killed and the
infinite tail beginning after `J` is one copy of `E`.  This proves `(EFS1)`.

The construction deliberately uses countably many named copies.  It is not a
finite-presentation compiler: conjugating all copies along one invertible
shift would identify their normal closures and make one event kill every
copy.

