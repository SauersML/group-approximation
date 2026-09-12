---
rg: 2
id: tracial-support-affine-linearization
kind: claim
title: The affine hull of a tracial BCS support is a perfectly tracial LCS relaxation
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

Let a finite Boolean constraint system have constraints
`C_i subset {0,1}^{V_i}` and let `tau` be a tracial satisfying representation
of its BCS algebra.  For each constraint, write its joint spectral PVM as

```text
1 = sum_(a in C_i) P_(i,a)
```

and define the tracial support

```text
S_i = {a in C_i : tau(P_(i,a)) > 0}.
```

Replace `C_i` by its affine hull `A_i=Aff_F2(S_i)`.  Since every affine subset
of a Boolean cube is the solution set of finitely many linear equations, the
family `(A_i)` is a finite linear constraint system after expanding each affine
hull into equations.

The original tracial representation satisfies this LCS perfectly.  Indeed,
a joint projection with zero trace is zero in the tracial GNS quotient, so the
spectral support of the commuting variables for constraint `i` is contained in
`S_i subset A_i`.  Every linear equation vanishing on `A_i` therefore holds as
an exact operator identity by finite joint functional calculus.

This construction is canonical relative to the chosen tracial state and is
strictly weaker than the original BCS: passing to affine hulls may add local
assignments.  No claim of `R^U`-soundness is made here.
