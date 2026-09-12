---
rg: 2
id: commutator-compressor-carries-no-wall
kind: claim
title: Commutator compressors carry no wall unless a factor has infinite growth
distinct_from:
  relative-wall-commutant-growth: That claim is an equivalence with no hypothesis on the compressor; this one is an obstruction that applies only to compressors expressible as commutators inside the compressor semigroup, and its conclusion is a quantitative infinite-index demand on the factors.
  compressor-growth-index-homomorphism: That claim states the multiplicative law of the growth index; this one is the group-theoretic consequence obtained by cancelling that law across a Steinberg relation, together with its concrete form for the monomial-cone pair.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

If `a,b` and `s=[a,b]` all lie in `P_Gamma` and `lambda(a),lambda(b)` are
finite, then `lambda(s)=1` and there is no relative wall for the compressor
`s`.  Reason: `ab=s b a` is one element with two factorizations inside
`P_Gamma`, and a multiplicative invariant with values in an abelian monoid
cannot survive the cancellation.

For the explicit Kun--Thom Theorem E pair
`Gamma=EL_r(F_q[x_1..x_d]) < G=EL_r(F_q[x^(+-1)]) semidirect SL_d(Z)`
(`r,d>=3`), every nonnegative matrix in `SL_d(Z)` is a compressor, so the
positive elementary transvections `u_(ij)(c)=I+c e_(ij)` lie in `P_Gamma`
and satisfy `[u_(ik)(a),u_(kj)(b)]=u_(ij)(ab)`.  This repository's explicit
compressor is `t=t_(u_12)` with ring image `F_q[x_1,x_1x_2,x_3,...,x_d]`,
and `u_12=[u_13,u_32]`.  Hence a wall there forces `lambda(u_13)=infinity`
or `lambda(u_32)=infinity`; and if every positive elementary transvection
has finite growth index then all have index `1` and no compressor in the
monoid they generate carries a wall.

This is the substitute for the Ore argument refuted by
`FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`: the compressor semigroup has no
fractions, but it does have commutators.
