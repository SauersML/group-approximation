---
rg: 2
id: fixed-sync-k-re-hardness-proof
kind: route
title: Freeze exactly-one hardness to the singleton-synchronization language
target: fixed-sync-k-language-is-re-hard
requires:
  - culf-mastel-subset-coded-exact-2csp-sync
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
---

For `k>=3`, the positive exactly-one relation

```text
C_k={e_1,...,e_k} subset {0,1}^k
```

is Boolean TVF: assigning two distinct coordinates the value `1` already
falsifies the relation.  Its classical CSP is NP-complete (the positive
one-in-`k` relation is outside every tractable Schaefer class for `k>=3`).
Culf--Mastel Theorem 7.31 therefore gives a constant `s<1` for which the
succinct constraint-variable perfect-versus-`s` problem for the fixed
language `{C_k}` is RE-complete.

Culf--Mastel Corollary 4.18 then expands this succinct hard family for the
same fixed source language `{C_k}` to finite non-succinct instances by a
computable exponential-time reduction while preserving a constant gap.

Now apply `culf-mastel-subset-coded-exact-2csp-sync` with `B={0}` to each
finite source instance.  It is a computable, defect-preserving map and every
target edge uses one of only

```text
D_j=({j}x{0}) union ((Z_k\{j})x(Z_k\{0})),
```

so the target language is the fixed `k`-relation language `SYNC_k`.  Perfect
completeness and the same constant soundness gap are preserved.  Hence the
finite `SYNC_k` perfect-versus-gap problem is RE-hard.  The reverse-Kleene
compiler only needs this computable hardness reduction; no membership
assertion is used.
