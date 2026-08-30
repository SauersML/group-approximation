---
rg: 2
id: stw63-all-z-embeddings-asymptotically-unitary
kind: claim
title: Any two unital Jiang--Su embeddings into any unital C-star algebra are asymptotically unitarily equivalent
root: true
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

For every unital C-star algebra `B` and unital embeddings `phi,psi:Z->B`,
there is a norm-continuous path `u:[0,infinity)->U(B)` such that

```text
||u(t) phi(z) u(t)^* - psi(z)|| -> 0                 (z in Z).
```

No condition is imposed on `u(0)`.  This is the stronger clause of STW
Problem LXIII and is an independent program target: it can fail even if the
approximate statement holds, because an implementing sequence need not admit
coherent approximately central connecting paths.

## Attempts

- Approximate equivalence supplies unrelated implementing unitaries, not a
  path.  Consecutive implementers differ by unitaries which approximately
  centralize `phi(Z)`.
- `approximate-to-asymptotic-via-central-paths` proves that controlled
  contractibility of all such approximately central transition unitaries is
  sufficient.  The unresolved issue is whether that property is automatic
  for a copy of `Z` in an arbitrary ambient algebra.
- K-theory of the embeddings cannot detect failure, by
  `z-embedding-invariants-collapse-before-cu`.  A path obstruction, if one
  exists after approximate equivalence, must instead live in the components
  of approximate relative commutants (or in a quotient by components supplied
  by the exact relative commutant).
