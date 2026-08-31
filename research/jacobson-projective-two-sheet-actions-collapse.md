---
rg: 2
id: jacobson-projective-two-sheet-actions-collapse
kind: claim
title: Every approximate projective two-sheet action of the Jacobson group collapses
distinct_from:
  two-sheet-projective-closure-forces-equivalent-carriers: that decides when a carrier produces a closed projective coefficient action; this proves that any such action is quantitatively trivial
  bounded-dimension-jacobson-head-has-algebraic-collapse: that only controls the marked head in an arbitrary bounded-dimensional tuple; this controls every generator of an SO(3)-valued tuple
  pauli-swap-coherence-reduces-to-the-commutant-gate: that treats the discrete C_2 normalizer quotient; this treats all continuous projective SU(2) rotations
---

Fix the finite presentation `P=<Sigma | R>` of `G=EL_28(J)`. There are
constants `C<infinity` and `alpha>0`, depending only on `P`, such that
every tuple `Q=(Q_s)_(s in Sigma)` in `SO(3)` satisfies

```text
max_(s in Sigma)||Q_s-I||_2
 <= C (max_(r in R)||r(Q)-I||_2)^alpha.                 (JPA1)
```

In particular every exact homomorphism

```text
EL_28(J) -> SO(3)
```

is trivial, and every relator-small projective `SU(2)` coefficient tuple
converges uniformly on the marked generators to the identity.

Combined with `two-sheet-projective-closure-forces-equivalent-carriers`,
this closes every macroscopic two-sheet rotation whose projective
coefficients form an approximate representation on their own. The only
surviving continuous ansatz is not an `SO(3)` microstate: it must use
inequivalent carrier isotypes so that nonscalar carrier intertwiners cancel
the projective relator errors.

DERIVATION
constant-subgroup-and-lojasiewicz-kill-so3-actions-proof
