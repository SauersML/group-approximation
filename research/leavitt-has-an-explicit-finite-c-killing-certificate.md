---
rg: 2
id: leavitt-has-an-explicit-finite-c-killing-certificate
kind: claim
title: Eight explicit native Leavitt words kill the coordinate cycle in every exact finite-dimensional unitary model
distinct_from:
  binary-leavitt-hyperlinear-iff-24k-feasible: That uses a computable exhaustion of the whole marked kernel to characterize hyperlinearity; this displays one fixed eight-word subset excluding exact finite-dimensional models, with no uniform bound for approximate models.
  leavitt-24k-kernel-packet-excludes-scalar-field-models: That four-word packet excludes specified elementary scalar-field models but has other exact finite models; this different packet kills the marked cycle in all exact finite-dimensional unitary models.
  thompson-v-has-no-nontrivial-fd-unitary-representation: That is the abstract representation theorem for V; this explicitly compiles its finite presentation into the fixed four Leavitt generators and links a killed swap to the coordinate cycle.
artifacts:
  - research/artifacts/leavitt-eight-word-reduction-and-s3-repair-2026-09-08.md
  - research/artifacts/leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md
  - research/artifacts/leavitt-nine-word-dag-verification-2026-09-08.json
---

Let `q:P=C_3*C_2^3 -> EL_3(L_(F_2)(1,2))` be the marked Leavitt
epimorphism, with generators `c,b_1,b_2,b_3` as in
`binary-leavitt-units-generated-by-c3-and-c2-cubed`.

There is the explicit set of eight words

```text
T_8={r_*,d^2,rho_2,rho_3,rho_5,rho_6,rho_7,rho_8}
```

defined by the finite straight-line formulas in Sections 1 and 3 of the
original compiler artifact, with the reduction proved in the new artifact,
such that `T_8` is contained in `ker q` and every word has length
at most `9880` in `c,c^(-1),b_1,b_2,b_3`. For every positive integer `n`
and every homomorphism `pi:P -> U(n)`,

```text
pi(T_8)=I  ==>  pi(c)=I.
```

Consequently the same holds for every homomorphism from `P` to a finite
group. These words may be adjoined to the existing four-word coefficient
packet or to the computable kernel exhaustion. In every fixed dimension
the frozen regular-factor model has positive minimum `T_8` defect.

For every unitary tuple, `rho_1` and `d^2` have equal defect, while
`rho_4=[L,r_*]` for the explicit word
`L=((A c)^(-1)c^(-1))^2`. Thus the old and new maximum defects satisfy
`E_8<=E_9<=2 E_8`, in both normalized HS and operator norm. The new
eight-word statement has a written proof; the linked executable replay
verifies the original nine-word compiler, not this subsequent reduction.

No lower bound uniform in dimension is asserted. This certificate does
not settle normalized-HS feasibility, hyperlinearity, or nonhyperlinearity.
