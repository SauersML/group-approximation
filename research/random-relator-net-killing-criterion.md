---
rg: 2
id: random-relator-net-killing-criterion
kind: claim
title: A summable random-relator return bound produces a nonhyperlinear presentation
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

Fix finitely many free generators, a finite short-word test set `F`, a
separation constant `delta>0`, a relator tolerance `eps>0`, and a finite
probability distribution on candidate relators of bounded length `L`.  Sample
`m` relators independently.  For every matrix size `n`, take an `eta`-net
`N_n` of the unitary tuples whose evaluations on distinct words of `F` are
`delta`-separated, with `L*eta` smaller than the radius slack, and put

```text
p_n(U) = Pr_r[ d_2(r(U),1) <= 2 eps ].
```

Suppose `SC` is an event on the sampled relator tuple such that every outcome
in `SC` presents a group in which the words of `F` remain distinct.  If

```text
sum_n sum_(U in N_n) p_n(U)^m < Pr(SC),
```

then at least one outcome in `SC` presents a group that is not hyperlinear.

The point is that the conclusion uses no stability-to-exact-representations
input.  It is a direct probabilistic-method obstruction to the existence of
normalized-HS microstates in any dimension.
