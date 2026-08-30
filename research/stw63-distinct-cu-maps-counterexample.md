---
rg: 2
id: stw63-distinct-cu-maps-counterexample
kind: claim
title: Two Jiang--Su embeddings into one unital algebra induce distinct Cuntz-semigroup maps
root: true
---

There are a unital C-star algebra `B` and unital embeddings
`phi,psi:Z->B` such that

```text
Cu(phi) != Cu(psi).
```

This would refute `stw99-problem-lxiii-z-embedding-uniqueness`, because
approximate unitary equivalence preserves the induced Cuntz-semigroup map.
It is marked as a separate root because constructing a counterexample is a
genuine program target, not a prerequisite expected to follow from the
positive uniqueness statement.

## Attempts

- `z-embedding-invariants-collapse-before-cu` shows why K-theory, traces and
  ideals cannot manufacture the difference.  The required distinction must
  occur among Cuntz classes having the same functional values and full ideal
  support.
- Abstractly writing two unit-preserving morphisms out of `Cu(Z)` is not
  enough: they must be realized by **embeddings into the same algebra**.
  Robert-type classification/realization results make stable-rank-one targets
  the natural arena, but the realization hypotheses and injectivity must both
  be checked.
- Villadsen/Toms stable-rank-one algebras remain the focused test family from
  STW Problem LXIV.  The unresolved calculation is whether their perforated
  or dimension-growth Cuntz data permits two coherent images of the soft
  part of `Cu(Z)` while fixing the compact unit.
