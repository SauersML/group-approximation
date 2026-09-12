---
rg: 2
id: uniform-finitary-support-makes-torsion-tracially-visible
kind: claim
title: A uniform locally finite support bound makes a surviving torsion mark visible in a tracial matrix model
distinct_from:
  torsion-normal-generator-has-full-support-corona-core: that gives operator-norm reblocking when the mark normally generates the entire finitely generated ambient group; this permits a proper locally finite normal subgroup and produces only normalized-Hilbert--Schmidt models on the compressed core.
  covariant-square-function-has-common-reducing-threshold: that gives the analytic coarea step for a supplied positive operator; this constructs rank-bounded cutoffs from normal finite subgroups and preserves every ambient group relation after compression.
artifacts:
  - research/artifacts/jacobson-surviving-head-has-a-tracial-core-2026-09-08.md
---

Let `G` be countable, let `A=union_j A_j` be a locally finite
normal subgroup with an increasing finite exhaustion, and let
`a in A_1` have finite order `m>=2`. Suppose a fixed `C<infinity`
satisfies

```text
codim Fix(sigma(A_j))<=C rank(sigma(a)-I)
```

for every finite-dimensional complex unitary representation of
every `A_j`. Every norm-corona homomorphism `rho` retaining `a`
then gives a homomorphism `psi` to a tracial matrix ultraproduct,
represented by normalized-Hilbert--Schmidt asymptotic unitary maps
`W_n:G->U(k_n)` satisfying

```text
W_n(a)^m=I,
rank(W_n(a)-I)/k_n>=1/C,
ker(rho)<=ker(psi).
```

In particular `||psi(a)-1||_2>=eta_m/sqrt(C)>0`, where `eta_m`
is the minimum distance from one of a nonidentity `m`th root of
unity. The conclusion is not operator-norm reblocking and does
not assert that `psi` is faithful on the whole ambient group.

DERIVATION
finite-support-coarea-and-polar-compression-proof
