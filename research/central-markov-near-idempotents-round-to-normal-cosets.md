---
rg: 2
id: central-markov-near-idempotents-round-to-normal-cosets
kind: claim
title: Central symmetric convolution near-idempotents round to normal-coset conditional expectations
distinct_from:
  schur-near-idempotents-round-dimension-uniformly: That rounds entrywise Schur multiplication to full coordinate matrix blocks; this rounds stochastic convolution on diagonal observables to algebras that can have arbitrarily large representation multiplicities.
  near-fixed-masas-round-channels-but-exclude-native-heat: That assumes a nearly fixed ambient maximal abelian algebra; the convolution channels here have diagonal image but need not fix that algebra pointwise.
artifacts:
  - research/artifacts/central-convolution-markov-rounding-2026-09-08.md
---

Let `G` be any finite group and `mu` a conjugation-invariant
probability measure satisfying `mu(g^-1)=mu(g)`. On the uniform
probability space `G`, define

```text
K f(x)=sum_g mu(g) f(g^-1 x),
delta=||K^2-K||_(infinity->2).
```

If `delta<sqrt(pi)/20`, there is a normal subgroup `N` of `G`
such that uniform averaging over its cosets satisfies

```text
||K-E_N||_(infinity->2) <= ||K-E_N||_(2->2)
                       <= (4/sqrt(pi))*delta.
```

For an abelian `G`, the stronger bound `2delta` holds whenever
`delta<1/10`, and the two displayed operator norms are equal.

The same estimates hold for the self-adjoint bistochastic UCP
matrix channel

```text
P_K(X)=diag(K(diag X))
```

and the trace-preserving conditional expectation onto

```text
B_N={diag(f): f is constant on N-cosets}
   = direct_sum_(G/N) C I_(|N|).
```

Thus the rounded algebra stays in the original matrix dimension
and may have nontrivial, unbounded multiplicity `|N|`. Neither
pointwise fixing of an ambient maximal abelian algebra nor
Schur multiplication is assumed. The theorem is restricted to
central convolution; arbitrary symmetric stochastic kernels,
general native heat rounding, and nonhyperlinearity are not
settled.
