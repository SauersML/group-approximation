---
rg: 2
id: finite-perfect-strategy-reduces-only-to-support-minimal-irrep
kind: claim
title: Finite perfect completeness reduces to a support-minimal irreducible block, not to a Fano cap
distinct_from:
  extreme-traces-and-local-pruning-do-not-select-fano-caps: that gives a concrete extreme full-support trace; this proves the exact positive reduction available from any finite-dimensional perfect strategy and identifies its limit as central rather than local support minimization.
  tracial-support-affine-linearization: that chooses an extreme trace in a zero-support face of the entire trace simplex; this decomposes one supplied finite-dimensional representation and does not range over unrelated perfect traces.
---

ESTABLISHED.
Let a finite BCS or CSP algebra have a perfect finite-dimensional
representation

```text
pi=direct_sum_(lambda in Lambda) pi_lambda tensor 1_(m_lambda),       (FPS1)
```

with irreducible `pi_lambda`.  Every summand is again perfect: all verifier
loss projections and algebraic relation residuals vanish as operators under
`pi`, hence vanish after central compression to a summand.  Since `Lambda`
is finite, one may choose a summand minimizing lexicographically the finite
list of local support cardinalities

```text
|{a:pi_lambda(P_(c,a))!=0}|.                                    (FPS2)
```

Its normalized matrix trace is an extreme perfect trace on the image factor.

This is the strongest support reduction supplied by finite-dimensionality
and irreducible block selection alone.  It deletes an atom only when that
atom vanishes on a central summand.  It cannot split a positive projection
inside a simple block or force a combinatorial property such as absence of a
Fano line.

The limit is sharp: the diagonal/Fourier representation

```text
C^7*C^7 -> M_7(C)                                                (FPS3)
```

from `extreme-traces-and-local-pruning-do-not-select-fano-caps` is already
irreducible, while all fourteen local atoms are nonzero.  It has one central
block and both local supports are the full unsafe seven-point relation.

Consequently Culf--Mastel's finite-dimensional HALT completeness permits
choosing a support-minimal irreducible perfect strategy, but no cited theorem
turns `(FPS2)` into the Fano-cap condition.  A positive proof must exploit
specific overlap relations of their constructed instance, not merely finite
dimension, factoriality, or block minimality.
