---
rg: 2
id: stw63-strongly-purely-infinite-targets-have-uniqueness
kind: claim
title: Unital strongly purely infinite targets have asymptotically unique Jiang--Su embeddings
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
distinct_from:
  stw63-locally-zstable-codomains-have-uniqueness: that encloses the two ranges in a Z-stable subalgebra and gives approximate uniqueness; this uses strong pure infiniteness of the target directly, does not assume a Z-stable hull, and gives asymptotic uniqueness.
  stw63-arbitrary-type3-vn-asymptotic-uniqueness: that establishes strong pure infiniteness for type-III von Neumann algebras; this is the general C-star target theorem to which that structural calculation reduces.
---

Let `B` be a unital strongly purely infinite C*-algebra.  Then any two
unital embeddings

```text
phi,psi:Z->B
```

are asymptotically unitarily equivalent.  Thus there is a norm-continuous
path of unitaries `(u_t)_(t>=0)` in `B` such that

```text
norm(u_t phi(z) u_t^* - psi(z)) -> 0                 (z in Z).
```

No simplicity, separability, nuclearity, exactness, stable-rank, Cuntz
comparison, or Z-stability hypothesis is imposed on `B`.  In particular,
this is an internal C*-target class rather than a von Neumann-shadow return
criterion.
