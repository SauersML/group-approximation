---
rg: 2
id: raw-amitsur-permutation-sampling-has-factorial-gap-loss
kind: claim
title: Raw local sampling of Amitsur permutation monomials loses the gap factorially
distinct_from:
  raw-gram-rank-overflow-has-no-constant-local-gap: that gives the general regular-simplex obstruction for dimension overflow; this identifies the permutation Gram table of the quaternion-corner Amitsur instruction with exactly that obstruction and computes the factorial query loss.
  quaternion-packet-internalizes-unitary-amitsur-corner: that gives an exact constant global residual tied to the marked word; this proves that sampling bounded windows of its alternating monomials cannot retain that constant.
  simple-algebraic-pcp-binary-local-test: that robustly tests a supplied encoded classical proof oracle; this rules out the proof-free strategy of querying raw permutation monomials and leaves an encoded global-sum proof as the necessary next layer.
  fixed-pi-degree-fingerprints-packet-label-factor: that uses one fixed polynomial degree, so its finitely many monomials may all be transported with a fixed constant; here the degree is endogenous and the number of monomials is factorially unbounded.
---

ESTABLISHED as a black-box local-testing obstruction.  Fix `n`, put

```text
m=2n,                         N=m!,
V_sigma=sgn(sigma) W_(sigma(1))...W_(sigma(m)).          (RAP1)
```

In the exact Fock completeness model, the `V_sigma` are isometries with
pairwise orthogonal ranges.  Their normalized Gram table is therefore

```text
G_F(sigma,tau)=delta_(sigma,tau),                        (RAP2)
```

and the normalized alternating energy is

```text
(1/N)||sum_sigma V_sigma||_2^2=1.                        (RAP3)
```

By contrast there are `N` unit vectors `v_sigma in C^(N-1)` with

```text
sum_sigma v_sigma=0,
<v_sigma,v_tau>=-1/(N-1)       for sigma!=tau.           (RAP4)
```

Thus their normalized global sum energy is zero, exactly as at the
dimension-matched Amitsur--Levitzki instruction, while every local Gram
window on at most `q` queried permutations differs from the corresponding
Fock window by operator norm at most

```text
(q-1)/(N-1)=(q-1)/((2n)!-1).                             (RAP5)
```

Consequently any randomized tester which queries at most `q` raw permutation
labels and applies an `L`-Lipschitz bounded predicate to their Gram matrix has
completeness--soundness separation at most

```text
L(q-1)/((2n)!-1).                                       (RAP6)
```

The same conclusion holds for any fixed equicontinuous family of bounded
local Gram predicates.  A constant robust gap therefore requires
`q=Omega((2n)!)`; choosing a random monomial, a random pair, or any fixed
number of random permutation windows cannot localize the exact residual of
`quaternion-packet-internalizes-unitary-amitsur-corner`.

For the most direct pair estimator the signal can be seen without a norm
bound.  The Fock off-diagonal expectation is zero, whereas `(RAP4)` has
off-diagonal expectation `-1/(N-1)`.  The entire unit change in `(RAP3)` is
spread uniformly over `N(N-1)` off-diagonal entries.

## Scope

The simplex vectors in `(RAP4)` are an abstract Gram completion; this claim
does not assert that they are simultaneous evaluations of the two word
variables `U_x,U_y`.  It rules out decoders whose only semantic input is a
bounded raw Gram window of the permutation monomials.  A successful compiler
may still introduce a redundant PCP proof of the global alternating sum and
test consistency between encoded proof coordinates.  The theorem shows that
such proof coordinates are essential: random sampling of the unencoded
monomial table cannot replace them.

Discontinuous exact-zero tests do not evade the conclusion in the setting at
issue.  Their modulus degenerates as `n` grows and hence they provide no
runtime-independent normalized-HS soundness estimate for approximate group
relations.

