---
rg: 2
id: commutation-stabilizers-are-relatively-embeddable
kind: claim
title: Exact projection commutation stabilizers in canonical CE models are scalar relatively embeddable
distinct_from:
  binary-coset-lamp-coefficient-forces-relative-embedding: That assumes an exact indicator-valued binary coefficient; this allows any involution and extracts its actual commutation subgroup from arbitrary element-dependent coefficients below one.
  relative-commutant-coset-field-removes-stabilizer: That quotients the stabilizer action in a different coset-field construction; this supplies normalized-HS conditional expectations and scalar relative embeddability.
artifacts:
  - research/artifacts/commutation-stabilizer-relative-embedding-2026-09-07.md
---

Let `A` be countable and let a CE finite tracial algebra contain a
canonical copy of `L(A)`, with group unitaries `u_g`. For a self-adjoint
unitary `s`, put `K={g in A:[s,u_g]=0}`. Then `L(K)<=L(A)` is relatively
embeddable over scalars.

The same conclusion holds for the common commutation stabilizer of
any countable family of projections. They need not commute with one
another and can initially belong to different canonical CE actor
models, combined using strictly positive weighted direct sums.

For one involution, the expectation coefficient is

```text
q_g=1-||[s,u_g]||_2^2/4 in [0,1].
```

It equals one exactly on `K`. Tensor amplification sends `q_g^k` to
zero for every fixed `g outside K`, without a uniform gap hypothesis.
The actor remains asymptotically multiplicative by choosing the
initial coordinate defects much smaller than `1/k`.
