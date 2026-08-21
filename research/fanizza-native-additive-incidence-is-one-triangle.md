---
rg: 2
id: fanizza-native-additive-incidence-is-one-triangle
kind: claim
title: Before the prescribed Pauli reduction, the native Fanizza incidence has one flat triangle
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that treats every context of the final BCS embedding and leaves an arbitrary collection of incidence cycles; this keeps the ordinary group and conjugacy equations as group equations and computes the incidence of only the genuinely additive native relations.
  join-tree-bcs-has-explicit-signed-hecke-atlas: that closes a running-intersection hypergraph; the native Fanizza hypergraph is not one because its terminal Pauli guard leaves the single chord computed here.
---

LIVE.  The six C18 signs must be retained.  The proposed global relation
`X_tilde Z_tilde X_tilde Z_tilde=J` is false at the terminal machine cell;
`fanizza-pauli-guard-switches-off-at-the-terminal-cell` shows that this failure
is exactly the halting switch in the completeness model.  Hence the
`Z_tilde` chord cannot be deleted and the incidence calculation below is the
native one.

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

In fact this sole cycle is **classically flat**.  The three separator signs

```text
(O_Q,O_P,Z_tilde) in {+1,-1}^3                         (FNI4)
```

commute pairwise: the pairs occur respectively in `C_D`, `C_R`, and `C_Z`.
Moreover every one of the eight assignments in `(FNI4)` extends to all four
contexts simultaneously.

For `C_X` and `C_Z`, when `O_Q=-1` choose the two compared signs equal, and
when `O_Q=+1` choose them arbitrarily.  For `C_D`, choose `O_D` to be the
Boolean conjunction of `O_P,O_Q`.  Finally write the first triple in `C_R`
as

```text
(O_P, X_tilde O_P X_tilde, U O_P U^*) .                (FNI5)
```

The bad set in those coordinates is

```text
A_123={(-,+,+),(+,-,+),(+,+,-),(-,-,+),(-,-,-)}.
```

If `O_P=+1`, choose the last two signs in `(FNI5)` as `(+,+)`; if
`O_P=-1`, choose them as `(+,-)`.  In either case `(FNI5)` lies outside
`A_123`, so the six-variable bad condition `A_123 x A_456` fails regardless
of the prescribed value of `Z_tilde` or of the remaining last-triple signs.
This proves the asserted extension.

Consequently no parity, contextuality, or marginal-compatibility
contradiction is carried by the native additive incidence cycle by itself.
Any successful groupification must use the fact that the private signs in
`(FNI1)` are **prescribed machine words**, rather than freely selectable
Boolean variables.  The unresolved obstruction is therefore semantic
word/corner realization, not combinatorial satisfiability of the triangle.

This combinatorial reduction does **not** yet give a group compiler.  A
signed-Hecke atlas for the four Boolean contexts must still identify its
corner involutions with the prescribed machine-group words in `(FNI1)`.
Treating those prescribed words as freely chosen finite-block signs would
discard the machine relations and is not a valid completion.
