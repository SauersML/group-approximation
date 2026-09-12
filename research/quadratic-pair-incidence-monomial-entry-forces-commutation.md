---
rg: 2
id: quadratic-pair-incidence-monomial-entry-forces-commutation
kind: claim
title: A quadratic pair-incidence monomial entry forces the two source projections to commute
distinct_from:
  harris-circulant-one-matrix-compiler-forces-affine-support: that classifies direct scalar pair-color encodings of the Harris completion; this rules out the next naive linearization in which pair products are promoted to auxiliary magic or monomial entries.
  elementary-abelian-harris-lift-compiles-bcs-consistency: that positively compiles affine overlap equality in the original magic block; this identifies when a quadratic auxiliary pair block is even a valid quantum-reflection block.
  oracularizable-tracial-nonru-game-exists: that supplies a perfect trace in which every sampled measurement pair commutes; this shows why the commutation forced here is safe on that chosen trace but not automatic in the universal source algebra.
---

**ESTABLISHED INCIDENCE LIMIT.**  Let `p,q` be projections in a star
algebra represented on a Hilbert space.  The product `pq` is a partial
isometry if and only if `p` and `q` commute.  In that case `pq` is itself a
projection.

Consequently, suppose a proposed pair-incidence completion of a magic
unitary `(e_(a,x))` introduces an auxiliary magic or finite-phase monomial
matrix whose entry is

```text
v_((a,b),(x,y))=e_(a,x)e_(b,y)                         (QPI1)
```

up to a nonzero scalar phase.  Every such encoded pair must satisfy

```text
[e_(a,x),e_(b,y)]=0.                                   (QPI2)
```

If `(QPI1)` is required for all pairs, the source projection algebra becomes
commutative and the game is classicalized.  If it is required only for the
question pairs sampled by an oracular game, it imposes exactly joint
measurability on those pairs; this may preserve a chosen perfect commuting
trace, but it is an additional quotient relation.

Thus auxiliary incidence vertices do not automatically linearize arbitrary
quadratic game relations into the fundamental monomial matrix.  A viable
compiler must first pass to an oracular commutation quotient and must still
encode the **pair-dependent forbidden support**.  Merely naming the products
as auxiliary entries is not that support encoding.
