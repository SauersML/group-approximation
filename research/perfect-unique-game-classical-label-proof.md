---
rg: 2
id: perfect-unique-game-classical-label-proof
kind: route
title: Transport one nonzero answer vector through the unique constraints
target: perfect-commuting-unique-game-is-classically-satisfiable
requires: []
---

Let `A_x^a` and `B_y^b` be the two projective measurements in a perfect
commuting strategy, acting on a unit vector `xi`.  On an edge `(x,y)`, zero
loss gives

```text
A_x^a B_y^b xi = 0 whenever b != pi_xy(a).              (UG1)
```

Using completeness of the two PVMs and bijectivity of `pi_xy`,

```text
A_x^a xi
  = A_x^a B_y^{pi_xy(a)} xi
  = B_y^{pi_xy(a)} xi.                                  (UG2)
```

Apply `(UG2)` successively along any path in the bipartite question graph.
In each connected component choose a question and an answer `a` for which
the corresponding vector piece is nonzero; one exists because the PVM sums
to the identity.  Transport `a` along paths using the edge permutations and
their inverses.

If two paths to the same question produced distinct answers `c != c'`,
`(UG2)` would identify the original nonzero vector with both orthogonal PVM
pieces at that question.  Their equality would force that vector to be zero,
a contradiction.  Hence path transport is independent of the chosen path.
The transported answers satisfy every edge permutation and give a perfect
deterministic labeling of that component.  Repeating over components proves
the claim.  The resulting one-dimensional strategy is finite-dimensional,
so a perfect-commuting-versus-finite-dimensional gap is impossible.
