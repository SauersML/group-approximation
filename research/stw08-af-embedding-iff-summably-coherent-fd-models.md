---
rg: 2
id: stw08-af-embedding-iff-summably-coherent-fd-models
kind: claim
title: AF-embeddability is exactly summable coherence of finite-dimensional models
distinct_from:
  stw99-problem-viii-exact-quasidiagonal-af-embeddable: that asks whether exactness and quasidiagonality force AF-embeddability; this theorem identifies the additional coherence an arbitrary quasidiagonal approximation must acquire.
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

Let `A` be a separable unital C\*-algebra and choose a dense sequence
`(a_j)` in its unit ball.  Then `A` is AF-embeddable if and only if there are
finite-dimensional unital C\*-algebras `F_n`, unital embeddings
`alpha_n:F_n->F_{n+1}`, u.c.p. maps `phi_n:A->F_n`, numbers `delta_n->0`,
and summable positive numbers `epsilon_n` such that

```text
max_(j,k<=n) ||phi_n(a_j a_k)-phi_n(a_j)phi_n(a_k)|| < delta_n,
max_(j<=n) | ||phi_n(a_j)||-||a_j|| | < delta_n,
||phi_(n+1)(a_j)-alpha_n(phi_n(a_j))|| < epsilon_n   (j<=n).
```

The first two lines are ordinary quasidiagonal finite-dimensional modelling.
The third, summable interstage-coherence line is the extra datum needed to
turn the models into one AF embedding.  The nonunital version follows by
unitizing `A`.
