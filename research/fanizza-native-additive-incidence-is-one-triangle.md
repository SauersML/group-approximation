---
rg: 2
id: fanizza-native-additive-incidence-is-one-triangle
kind: claim
title: The native Fanizza algebra has only one cyclic additive incidence cell
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that treats every context of the final BCS embedding and leaves an arbitrary collection of incidence cycles; this keeps the ordinary group and conjugacy equations as group equations and computes the incidence of only the genuinely additive native relations.
  join-tree-bcs-has-explicit-signed-hecke-atlas: that closes a running-intersection hypergraph; the native Fanizza additive hypergraph misses running intersection by exactly one triangle chord.
---

Keep the involution, group, commutation, and conjugacy equations in the
presentation of `A_L(m)` as multiplicative equations.  The remaining native
additive equations are represented by four Boolean contexts:

```text
C_X = {O_Q, X_(m,0), X_tilde},
C_Z = {O_Q, Z_(m,0), Z_tilde},
C_D = {O_D, O_P, O_Q},
C_R = {O_P, X_tilde O_P X_tilde, U O_P U^*,
       J, X_tilde Z_tilde X_tilde, Z_tilde}.          (FNI1)
```

Here `C_X,C_Z` are the two conditional-equality constraints, `C_D` is
`D=PQ`, and `C_R` is the six-variable recurrence predicate.  Nested
conjugacy monomials in `(FNI1)` are treated as the indicated words, rather
than as additional independent contexts.

The context-intersection graph has the following nonempty shared-variable
edges:

```text
C_X -- C_D : O_Q,
C_Z -- C_D : O_Q,
C_D -- C_R : O_P,
C_Z -- C_R : Z_tilde.                                 (FNI2)
```

There are no other shared native Boolean variables.  Hence `C_X` is a leaf
and the entire failure of running intersection is the one triangle

```text
C_Z --(O_Q)-- C_D --(O_P)-- C_R --(Z_tilde)-- C_Z.    (FNI3)
```

Indeed, deleting either of the last three edges gives a join tree.  Conversely
no join tree exists: connectedness of the contexts containing each of the
three variables in `(FNI3)` forces all three triangle edges.

Thus groupifying the native Fanizza signal does not require solving the full
cyclic BCS atlas problem.  After ordinary equations remain multiplicative,
the additive compatibility problem has exactly one cyclic cell, with binary
separators, and one attached leaf.

This combinatorial reduction does **not** yet give a group compiler.  A
signed-Hecke atlas for the four Boolean contexts must still identify its
corner involutions with the prescribed machine-group words in `(FNI1)`.
Treating those prescribed words as freely chosen finite-block signs would
discard the machine relations and is not a valid completion.
