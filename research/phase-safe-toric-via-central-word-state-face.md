---
rg: 2
id: phase-safe-toric-via-central-word-state-face
kind: route
title: Compile the fixed non-RU trace into the relative finite-dimensional central-word face
target: phase-safe-toric-gap-game-exists
requires:
  - mipstar-bcs-tracial-nonru-exists
  - toric-gap-is-a-relative-fd-central-word-face
  - central-word-state-face-compiler
---

Use the established BCS tracial/non-`R^U` separation as the source and apply
`central-word-state-face-compiler`.  It supplies a finite torically determined
game, a finite phase group `B`, and clause words `beta_i a_i b_i`.

Property 1 of the compiler supplies a tracial state whose GNS cyclic vector
is fixed by every clause.  Toric determination therefore makes this a
perfect commuting-operator strategy, so

```text
omega_qc=1.                                               (CWF1)
```

The same representation is faithful on the scalar copy of `B` and factors
through the quotient by the normal closure `N` of the clauses.  Hence

```text
N intersect B={1}.                                       (CWF2)
```

Property 2 says that the clause-character face is disjoint from the weak-star
closure of finite-dimensional vector states.  By the established relative-FD
face criterion in `toric-gap-is-a-relative-fd-central-word-face`, this is
equivalent to

```text
omega_qa<1.                                               (CWF3)
```

Equations `(CWF1)--(CWF3)` are exactly
`phase-safe-toric-gap-game-exists`.

The neighboring finite-Morita, spherical-root, extraspecial-spin,
product-stabilizer, malnormal-subgroup, and raw-GNS-kernel results are
obstructions to proposed proofs of the compiler.  They are not logical
premises of this implication and therefore do not belong in `requires`.
