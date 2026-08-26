---
rg: 2
id: higman-fourth-return-jointly-centralizes-clock
kind: claim
title: A fourth-return matcher asymptotically centralizes both periodic clock generators
artifacts:
  - research/higman-fourth-return-jointly-centralizes-clock-proof.md
distinct_from:
  periodic-higman-clock-centralizer-has-linear-width: that computes the full commutant of the permutation clock P and leaves 2q-1 real gauge dimensions; this proves that the fourth return is simultaneously almost central for P and D, and computes their much smaller exact joint commutant.
  order-four-bs-matcher-builds-higman-opnorm-microstate: that turns a vanishing matcher and return error into a Higman microstate; this identifies the algebra in which the fourth power would have to asymptotically live, without asserting that almost-central matrices are operator-norm close to that algebra.
---

**ESTABLISHED.**  Let `P,D,K` be finite-dimensional unitaries with

```text
P D P^* = D^2,
epsilon = ||D-K P K^*||_op,
r       = ||K^4 P K^(-4)-P||_op,                     (HJC1)
```

and put `C=K^4`.  Then

```text
||[C,P]||_op = r,
||[C,D]||_op <= r+2epsilon.                          (HJC2)
```

Thus every solution of the remaining order-four matcher gate makes its
fourth power an operator-norm asymptotic central sequence for the **whole**
exact Baumslag--Solitar packet, not merely for its conjugator `P`.

For the periodic packet of `periodic-higman-bs-clocks-have-three-opnorm-small-seams`,
where `q=3^n`, `D e_x=exp(2 pi i x/q)e_x`, and
`P e_x=e_(2^(-1)x)`, the exact joint commutant is

```text
{P,D}'
 = {diag(c_x) : c_(2^(-1)x)=c_x for every x}
 ~= C^(n+1).                                         (HJC3)
```

Its unitary group is an `(n+1)`-torus.  Hence the fourth-return condition
cuts the visible exact gauge algebra from the `2q-1`-dimensional commutant
of `P` alone down to logarithmic dimension `n+1` once simultaneous
centrality is imposed.

This is a reduction, not a proof that the gate is impossible.  In
particular `(HJC2)` does **not** give a dimension-independent operator-norm
estimate of `dist(K^4,{P,D}')` for an arbitrary return rate.
`periodic-clock-p-commutant-has-uniform-joint-gap` does give such an estimate
when `P`-commutation is exact, and when `3^n r->0`; the unrestricted gate has
only `r->0`.  Moreover
`periodic-clock-has-opnorm-almost-central-fourth-power-escape` constructs
unitary fourth powers with both commutators vanishing but fixed distance from
the joint commutant, so simultaneous centrality alone cannot remove that
rate seam.  Control of the **same** fourth root as a spectral matcher is
still absent.  The claim therefore rules out treating the full
`2q-1`-dimensional `P`-centralizer as free return gauge, while leaving slow
exceptional arithmetic matchers open.
