---
rg: 2
id: sl3-canonical-double-has-a-correctable-vertex
kind: claim
title: Every canonical microstate of the SL3 arithmetic double has at least one correctable ambient vertex
artifacts:
  - research/artifacts/sl3-double-frobenius-normalization-audit-2026-08-21.md
distinct_from:
  sl3-double-one-near-vertex-forces-joint-near-exactness: that starts from one correctable vertex and corrects the other; this is the minimal missing source of that first anchor.
  sl3z-regular-microstates-are-congruence-correctable: that asks to correct a regular microstate of the lattice C; this asks for one full A vertex in a canonical microstate of A amalgamated over C with A.
  sln-z-flexibly-hs-stable: that quantifies over all almost representations of one lattice; this is restricted to the two vertex marginals occurring in canonical-character microstates of one fixed double.
---

OPEN.  Let

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),       D=A *_C A.
```

For every canonical-character normalized-Hilbert--Schmidt microstate
sequence `sigma_n` of `D`, with vertex restrictions `pi_(n,0),pi_(n,1)`,
there are indices `j_n in {0,1}` and exact finite-dimensional unitary
representations `alpha_n:A->U(d_n)` such that

```text
max_(x in S_A)||pi_(n,j_n)(x)-alpha_n(x)||_2 -> 0.           (CDV1)
```

The index may vary with `n`; passing to a subsequence makes it constant.
This is the minimal correction statement left by the arithmetic-double
reduction.  Once `(CDV1)` supplies an anchor,
`sl3-double-one-near-vertex-forces-joint-near-exactness` corrects the other
vertex to the same representation, and the fold mark collapses.

The current 2-Kazhdan/Frobenius-stability literature does not prove
`(CDV1)`.  `sl3-canonical-double-replication-escapes-every-frobenius-basin`
shows that canonical trace cannot convert normalized defect into the
unnormalized Frobenius-small hypothesis: replicas preserve every hypothesis
of `(CDV1)` while making unnormalized defects arbitrarily large.  A proof
must therefore be native to normalized HS, or supply a global
replica-homogeneous correction inequality rather than invoke qualitative
Frobenius stability.

