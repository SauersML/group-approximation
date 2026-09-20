---
rg: 2
id: hrf-sym4-composition-sector-proof
kind: route
title: Split the vertex extensions and restrict to a nontrivial central eigenspace
target: hrf-sym4-composition-sector-kills-five-mark
requires:
  - hrf-sym4-isotypic-modules-are-semisimple
  - hrf-amplified-sym4-five-twists-have-no-detectors
---

The first prerequisite makes each vertex restriction a direct sum of V,
where V=Sym^4(K^2). Extend scalars to an algebraic closure of K. The
explicit irreducibility argument in that prerequisite shows V is
absolutely simple, so the extended vertex modules still have only V
as composition factors.

Since Z is central and Z^5=I in characteristic 19, its action is
diagonalizable and every eigenspace is invariant under the entire
triangle. If Z is not I, choose a nonzero eigenspace with eigenvalue
lambda not equal to one. Each vertex restriction on this submodule
has only V as composition factors, hence is a direct sum V^m by the
first prerequisite. Its common positive dimension forces the same m
at each vertex. The central mark acts there as the nontrivial scalar
lambda. This contradicts the second prerequisite, which covers every
positive m and every nonzero twist. Thus Z=I after scalar extension,
and therefore already over K.
