---
rg: 2
id: periodic-clock-p-commutant-has-uniform-joint-gap
kind: claim
title: The periodic clock P-commutant has a dimension-free operator-norm gap to the joint commutant
artifacts:
  - research/periodic-clock-p-commutant-has-uniform-joint-gap-proof.md
distinct_from:
  periodic-higman-clock-centralizer-has-linear-width: that counts the dimension of the full P-commutant; this gives a dimension-independent quantitative projection from that commutant to the much smaller joint commutant using the D-commutator.
  higman-fourth-return-jointly-centralizes-clock: that proves K^4 almost commutes with P and D; this supplies an operator-norm correction only when P-commutation is exact, plus a rate-dependent corollary for approximate return.
---

**ESTABLISHED.**  Let `q=3^n`, and on `C^(Z/qZ)` put

```text
D e_x=exp(2 pi i x/q)e_x,
P e_x=e_(2^(-1)x).                                   (PCG1)
```

For every matrix `X` commuting with `P`, there is a matrix
`Z in {P,D}'` such that

```text
||X-Z||_op <= 2 ||[X,D]||_op.                        (PCG2)
```

The constant `2` is independent of `n` and of the matrix dimension.  Thus,
although `{P}'` has complex dimension `2q-1`, it has a uniform
operator-norm spectral gap transverse to

```text
{P,D}' ~= C^(n+1).                                   (PCG3)
```

As a consequence, in the matcher notation of
`higman-fourth-return-jointly-centralizes-clock`, if the fourth return is
exact (`r=0`), then

```text
dist(K^4,{P,D}') <= 4epsilon.                        (PCG4)
```

More generally let `L=2*3^(n-1)`, the order of `P`.  Averaging `K^4` over
`<P>` and applying `(PCG2)` gives

```text
dist(K^4,{P,D}')
 <= (5/2)(L-1)r + 2r + 4epsilon.                    (PCG5)
```

In particular any candidate with `Lr->0` and `epsilon->0` has its fourth
power asymptotically in the logarithmic-dimensional joint commutant.

This still does not settle the matcher gate.  Its hypothesis asks only
`r->0`, with no rate relative to `L`, and `(PCG2)` applies directly only
after exact `P`-commutation.  Nor does closeness of `K^4` to `{P,D}'` by
itself provide a compatible fourth-root correction of `K`.  The theorem
therefore isolates the remaining slow-return/root-compatibility seam rather
than claiming Higman collapse.  The exactness cannot be dropped formally:
`periodic-clock-has-opnorm-almost-central-fourth-power-escape` gives unitary
fourth powers with both commutators tending to zero while their distance to
the joint commutant stays at least one.
