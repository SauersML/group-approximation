---
rg: 2
id: stw82-af-coefficient-toeplitz-maximum
kind: claim
title: Toeplitz extensions with arbitrary AF coefficients obey the maximum formula nonquasidiagonally
distinct_from:
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that proves raw complementary-cut reuse gives only quasidiagonal extensions; the present extensions have nonzero index and are not quasidiagonal, but attain the maximum by finite-stage transition absorption.
  stw82-one-dimensional-middle-forces-maximum: that assumes the middle algebra is already known to have dimension at most one; this computes that dimension for a new coefficient family.
artifacts:
  - research/artifacts/stw82-one-color-gluing-audit-2026-08-30.md
  - research/artifacts/stw82-projectional-cut-obstruction-audit-2026-08-30.md
---

Let `A` be a nonzero separable unital AF algebra, let `N>=1`, let `S` be the
unilateral shift, and put

```text
T_N=C*(S^N,K) subset B(ell^2(N_0)).
```

Tensoring the index-`N` Toeplitz extension with `A` gives

```text
0 -> K tensor A -> T_N tensor A -> C(T) tensor A -> 0.  (AF-T)
```

Its three nuclear dimensions are exactly

```text
dim_nuc(K tensor A)=0,
dim_nuc(C(T) tensor A)=1,
dim_nuc(T_N tensor A)=1.                               (1)
```

Consequently `(AF-T)` satisfies the extension maximum formula.

This is a genuinely nonprojectional positive class.  The boundary map of
`(AF-T)` satisfies

```text
partial([z] tensor [1_A])=+- N[1_A]
       in K_0(K tensor A)=K_0(A),                      (2)
```

which is nonzero.  Hence `(AF-T)` is not a quasidiagonal extension and has
no quasicentral approximate unit of projections.  By
`stw82-raw-two-cut-reuse-iff-quasidiagonal`, its two raw complementary cuts
cannot be asymptotically orthogonalized.

The optimal two-colour approximation instead comes from replacement at
finite AF stages: each stage is a finite direct sum of matrix amplifications
of the scalar index-`N` Toeplitz algebra, where the transition band is
already absorbed by the scalar Toeplitz construction.  Thus the maximum can
hold uniformly through a nonzero index obstruction without any projectional
cut.
