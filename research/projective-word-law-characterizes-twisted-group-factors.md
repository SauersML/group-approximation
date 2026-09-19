---
rg: 2
id: projective-word-law-characterizes-twisted-group-factors
kind: claim
title: A separable finite factor has projective-word generators exactly when it is a twisted group factor
distinct_from:
  projective-basis-character-criterion: that begins with a specified group character and tests its GNS unitaries; this is the intrinsic existential characterization of a factor by some countable generating sequence.
  cdi-noncartan-bridge-has-two-exact-gates: that applies the criterion to one specified CDI character and adds finite-phase torsion; this characterizes when any alternative generating sequence can satisfy the first gate.
---

Let `(M,tau)` be a finite factor with separable predual.  The following are
equivalent.

1. There is a finite or countable sequence of unitaries `(u_j)` generating
   `M` such that every group word `w` satisfies

   ```text
   tau(w(u))=0  or  |tau(w(u))|=1.                     (PWL1)
   ```

2. There are a countable group `Gamma` and a scalar multiplier
   `omega in Z^2(Gamma,T)` such that

   ```text
   (M,tau) isomorphic_to (L_omega(Gamma),tau_omega)     (PWL2)
   ```

   trace-preservingly.

Equivalently, `(M,tau)` has a countable orthonormal unitary basis closed
under multiplication up to scalar phases.  If the phase group can be chosen
finite, the multiplier is finite-valued and `M` is a canonical central corner
of a finite central extension.  Without finite phases `(PWL2)` is only a
twisted group-factor realization and does not by itself give a positive-trace
corner of an ordinary countable group factor.

