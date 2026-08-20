---
rg: 2
id: augmentation-one-corner-retains-a-character
kind: claim
title: Every augmentation-one algebraic group corner retains a unital scalar character
artifacts:
  - research/artifacts/signed-hecke-direct-trace-promotion-2026-08-20.md
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that uses positive Plancherel mass in the canonical trace to obstruct a universal trace identity; this uses the scalar augmentation character and rules out the corner homomorphism before traces enter.
---

Let `epsilon:C[Gamma]->C` be augmentation and let `q=q^*=q^2` be an
algebraic projection. Then `epsilon(q)` is a scalar self-adjoint idempotent,
so it is `0` or `1`. If `epsilon(q)=1`, restriction gives a unital star
character

```text
epsilon_q:qC[Gamma]q -> C.                               (AOC1)
```

Consequently no unital star algebra without characters can map unitally into
such a corner. In particular the subgroup-average projection

```text
p_K=|K|^(-1) sum_(k in K) k
```

has augmentation one, so a classically unsatisfiable BCS algebra cannot have
a unital model in `p_K C[Gamma]p_K`: composing with `(AOC1)` would be a
classical satisfying assignment.
