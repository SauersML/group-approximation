---
rg: 2
id: stw09-full-matrix-coherence-rational-core-criterion
kind: claim
title: Full-matrix coherence of an exact finite-dimensional core is equivalent to rational central trace weights
distinct_from:
  stw10-qd-traces-admit-exact-finite-dimensional-core-models: that theorem makes each independent quasidiagonal model exact on a prescribed core; this theorem determines exactly when those core representations can be connected through full-matrix embeddings, and exposes a rational-rank obstruction absent from coordinatewise exactification
  stw09-trace-preserving-af-embedding-iff-trace-coherent-models: that criterion permits arbitrary finite-dimensional target algebras and arbitrary compatible traces; this theorem restricts to full matrix targets with normalized traces and proves that this tempting restriction already fails for irrational traces on C^2
  stw08-af-embedding-iff-summably-coherent-fd-models: that untraced criterion uses norm detection and arbitrary finite-dimensional stages; this is a traced local criterion on one exact core whose obstruction is normalized matrix rank
artifacts:
  - research/artifacts/stw09-matrix-coherence-rank-obstruction-2026-08-30.md
---

Let

```text
E = direct_sum_(j=1)^s M_(d_j)
```

be a finite-dimensional unital C-star algebra, let `z_j` be its minimal
central projections, and let `tau` be a faithful trace on `E`.  The following
are equivalent:

1. there are full matrix algebras `M_(k_n)`, unital star homomorphisms
   `rho_n:E->M_(k_n)`, and unital embeddings
   `alpha_n:M_(k_n)->M_(k_(n+1))` such that

   ```text
   tr_(k_n) rho_n(x) -> tau(x)                         (x in E),
   ||rho_(n+1)(x)-alpha_n(rho_n(x))|| -> 0             (x in E);
   ```

2. `tau(z_j)` is rational for every `j`.

In fact, in (1) the normalized ranks
`tr_(k_n)(rho_n(z_j))` are eventually constant for every `j`.  Therefore the
same obstruction holds if the coherence errors are summable, or merely drop
below `1` eventually on the central projections.

Consequently, let `E subset A` be a unital finite-dimensional subalgebra and
let matrix-valued u.c.p. trace models `psi_n:A->M_(k_n)` satisfy
`E subset MD(psi_n)`.  If the `psi_n` can be coherified through unital
embeddings of their full matrix targets with norm error tending to zero on
`E`, then the limiting trace has rational weight on every minimal central
projection of `E`.

