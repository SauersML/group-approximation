---
rg: 2
id: stw09-trace-preserving-af-embedding-iff-trace-coherent-models
kind: claim
title: A faithful trace extends across an AF embedding exactly when its finite models are trace-coherent
distinct_from:
  stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable: that asks only for some AF embedding from a faithful quasidiagonal trace; this criterion concerns the stronger conclusion that the specified trace extends to the AF target.
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

Let `A` be separable and unital and let `tau` be a faithful tracial state.
There is a
unital embedding `Phi:A->E` into a unital AF algebra and a trace `sigma on E`
with `sigma Phi=tau` if and only if there are finite-dimensional unital
C\*-algebras `F_n`, unital embeddings `alpha_n:F_n->F_{n+1}`, traces
`sigma_n on F_n`, and u.c.p. maps `phi_n:A->F_n` such that

```text
sigma_(n+1) alpha_n = sigma_n,
sigma_n phi_n(a) -> tau(a),
phi_n(ab)-phi_n(a)phi_n(b) -> 0,
```

for all `a,b in A`, and, for one fixed dense sequence `(a_j)` in `A`,

```text
||phi_(n+1)(a_j)-alpha_n(phi_n(a_j))|| <= epsilon_n
                                                    (j<=n),
```

where `sum epsilon_n<infinity`.  Equivalently, one may use growing finite
tests whose union is dense.

No separate asymptotic-isometry assumption is needed: faithfulness of `tau`
makes the resulting trace-preserving homomorphism automatically injective.
