---
rg: 2
title: STW LXXXII projectional-cut obstruction and current-literature audit (2026-08-30)
kind: artifact
---

# Source statement and hypothesis ledger

Problem LXXXII asks, for every extension `0 -> I -> E -> D -> 0`, whether

```text
dim_nuc(E)=max(dim_nuc(I),dim_nuc(D)).
```

The general theorem of Winter--Zacharias gives only the sum bound

```text
dim_nuc(E) <= dim_nuc(I)+dim_nuc(D)+1.
```

The `+1` here is part of a sum of **numbers of colours**; it must not be
silently carried into a claimed maximum theorem.

The directly targeted primary papers checked were:

- Winter--Zacharias, *The nuclear dimension of C*-algebras*, Proposition
  2.9, [arXiv:0903.4914](https://arxiv.org/abs/0903.4914);
- Evington, *Nuclear dimension of extensions of O-infinity-stable
  algebras*, [arXiv:2012.03650v3](https://arxiv.org/abs/2012.03650v3);
- Gardner--Tikuisis, *The nuclear dimension of extensions of commutative
  C*-algebras by the compact operators*,
  [arXiv:2202.04695v2](https://arxiv.org/abs/2202.04695v2);
- Evington--Ng--Sims--White, *Nuclear dimension of extensions of
  commutative C*-algebras by Kirchberg algebras*,
  [arXiv:2409.12872v2](https://arxiv.org/abs/2409.12872v2), especially
  (1.2), the positive-case list on pp. 2--3, and Theorem B.

An arXiv API title/abstract search for `"nuclear dimension" AND extension`,
sorted by submission date and run on 2026-08-30, returned the 2025 revision
of Evington--Ng--Sims--White as the newest directly targeted operator-algebra
paper.  No primary source located in that screen claims the arbitrary
maximum theorem.  Thus the root remains open; the statements below are
new reductions, not a literature claim that LXXXII is solved.

# New exact obstruction equivalence

For a separable extension, the following are equivalent:

1. the ideal has a quasicentral approximate unit of projections;
2. it has a positive contractive quasicentral almost-idempotent approximate
   unit `(h_n)`, with `h_(n+1)h_n=h_n`, such that
   `norm(h_n-h_n^2) -> 0`;
3. along such an approximate unit, the complementary supports `h_n` and
   `1-h_n` can be perturbed in norm to orthogonal positive contractions.

The spectral projection `p_n=chi_[1/2,1](h_n)` lies in the ideal because
the cutoff vanishes at zero.  The almost-idempotent relation makes these
spectral projections increasing, while norm closeness preserves the
approximate-unit and quasicentral properties.  This proves that asymptotic orthogonalization
of the **raw two cuts** is not a new general colour-reuse method: it is
exactly quasidiagonality of the extension, a case already covered by the
known maximum theorem.

This is deliberately narrower than the maximum formula.  Gardner--Tikuisis
and Evington--Ng--Sims--White obtain optimal bounds in non-quasidiagonal
settings by splitting and reorganizing a transition band and using map
classification.  The Toeplitz and interval examples likewise forbid the
false inference that nonprojectional cuts obstruct the formula itself.

# New unconditional positive class

Every ideal--quotient decomposition of a separable algebra `E` with
`dim_nuc(E)<=1` obeys the maximum formula.  Endpoint dimensions are at most
one.  If their maximum is one, monotonicity gives equality.  If it is zero,
both endpoints are AF, extension closure makes `E` AF, and equality again
follows.  Consequently every counterexample has `dim_nuc(E)>=2`.

This is a middle-algebra class, not an endpoint gluing hypothesis.  It may
be combined without further colour bookkeeping with any independent
dimension-one theorem.  For example, the 2026 preprint
[arXiv:2607.27691](https://arxiv.org/abs/2607.27691) announces nuclear
dimension one for a non-simple purely infinite higher-rank-graph class;
whenever that theorem applies to `E`, all of its ideal extensions satisfy
the maximum formula automatically.  This citation is not needed for the
abstract result.

# Exact remaining universal hinge

Earlier repository reductions show that a counterexample exists if and
only if one exists among separable stable extensions with essential ideal.
The new equivalence rules out only one strategy there: perturbing a generic
quasicentral approximate unit until the two complementary raw supports can
share colours.  That is possible exactly for quasidiagonal extensions.

The remaining universal hinge is therefore:

> For a separable stable essential non-quasidiagonal extension, construct
> finite-dimensional approximations in which the transition band is
> redistributed among `max(dim_nuc(I),dim_nuc(D))+1` order-zero colours,
> without requiring the two raw complementary supports to become
> orthogonal.

Existing successful proofs pay for this redistribution with strong
classification hypotheses.  No source or argument checked here supplies
it for arbitrary endpoint algebras.
