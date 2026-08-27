---
rg: 2
id: factor-split-projective-kernel-face-meets-fd-closure
kind: claim
title: Every scalar projective-kernel face of a split factorial game representation meets the finite-dimensional closure
artifacts:
  - research/artifacts/monomial-toric-factor-clause-audit-2026-08-23.md
distinct_from:
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that gives examples showing one non-CE trace need not exclude other states in its face; this proves a universal product-state obstruction for the split factorial representation of a two-player game.
  normal-phase-safe-toric-games-have-qa-one: that starts from finitely many normal toric clauses; this applies even to an infinite projective kernel before compactification or game testability.
  monomial-finite-phase-ce-kernel-face-gap: that asks for exclusion of CE tracial states; the product state here need not be tracial or CE, so that stronger direct group route is not refuted.
---

**ESTABLISHED.**  Let `tau` be an extreme trace of a two-player game algebra,
so its standard representation is

```text
pi(a,b)=L(A_a)R(B_b) on L^2(M,tau)                     (FSK1)
```

for a factor `M`.  Let `K <= G_A x G_B` and suppose a character `chi`
satisfies `pi(k)=chi(k)I` for every `k in K`.  Then

```text
F_(K,chi) intersects closure(S_fd(G_A x G_B)) != empty. (FSK2)
```

Indeed, for `k=(a,b)`, `(FSK1)` gives

```text
L(A_a)=chi(k)R(B_b)^*.
```

The left and right copies of a factor intersect only in the scalars.  Hence
`A_a` and `B_b` are scalar separately.  Restricting the source states to the
two player groups therefore gives scalar characters on all projected clause
words, and their product state has exactly the scalar value `chi(k)` for
every `k in K` (up to the inverse convention in the definition of
`F_(K,chi)`).  Thus that product state belongs to the projective-kernel face.

Both one-player full group C-star algebras are RFD, so their arbitrary states
are weak-star limits of finite-dimensional vector states.  Tensoring the two
approximating nets places the product state in
`closure(S_fd(G_A x G_B))`, proving `(FSK2)`.  Therefore no projective kernel
extracted from an extreme monomial trace can satisfy the proposed whole-face
finite-dimensional separation.

