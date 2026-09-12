---
rg: 2
id: fixed-nonru-independent-set-game-proof
kind: route
title: Apply the sharp synchronous independent-set reduction to the fixed non-RU game
target: fixed-nonru-independent-set-orthogonality-game-exists
requires:
  - oracularizable-tracial-nonru-game-exists
  - synchronous-independent-set-reduction-preserves-a-quadratic-gap
---

Take the fixed synchronous game `G_cv` with perfect commuting value and
finite-dimensional gap `epsilon>0`.  Apply the independent-set construction.
Perfect commuting play maps to a perfect tracial strategy for `I(G_cv)`.
The synchronous reverse estimate gives a target gap at least
`zeta epsilon^2/t`; set this constant to `delta_0`.  Formula `(SIG2)` is
exactly `(NIS2)`.

