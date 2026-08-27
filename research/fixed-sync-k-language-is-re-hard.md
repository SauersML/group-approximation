---
rg: 2
id: fixed-sync-k-language-is-re-hard
kind: claim
title: A fixed k-relation singleton-synchronization 2-CSP language is RE-hard for every k at least three
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
distinct_from:
  culf-mastel-subset-coded-exact-2csp-sync: that proves the local compiler; this combines it with the Boolean-TVF theorem and freezes the target to only k relations.
  culf-mastel-oracular-2csp-perfect-gap-family: that permits arbitrary 2-CSP predicates; this target contains only singleton-synchronization relations.
---

**ESTABLISHED.**  For every `k>=3`, put

```text
C_k={e_1,...,e_k} subset {0,1}^k
```

and define the fixed alphabet-`k` binary language

```text
SYNC_k={D_0,...,D_(k-1)},
D_j=({j}x{0}) union ((Z_k\{j})x(Z_k\{0})).             (SYN1)
```

The predicate `C_k` is TVF: setting any two distinct coordinates to `1`
falsifies it regardless of the remaining coordinates.  It is NP-complete by
Schaefer's theorem.  Neither constant is accepted; `AND(e_1,e_2)=0`;
`OR(e_1,e_2)` has two ones; `MAJ(e_1,e_2,e_3)=0`; and
`MIN(e_1,e_2,e_3)` has three ones.

Culf--Mastel Theorem 7.31 therefore supplies a constant-gap RE-hard family
for the fixed positive exactly-one predicate in the constraint-variable
model.  Applying `culf-mastel-subset-coded-exact-2csp-sync` with `B={0}`
preserves the defect exactly and uses only `(SYN1)`.  Hence perfect versus
constant-gap finite-dimensional value is RE-hard for succinct `SYNC_k`
instances.  Corollary 4.18 expands the succinct instances in computable
exponential time to finite non-succinct instances, which is sufficient for
the reverse-Kleene compiler.

The conclusion here is RE-hardness.  No separate membership assertion is
needed for the non-hyperlinear route.
