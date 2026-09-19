---
rg: 2
id: stw81-zero-dimensional-simple-field-proof
kind: route
title: Refine the bundle charts by clopen pieces and compute each AF tensor fibre
target: stw81-zero-dim-simple-fields-obey-trichotomy
requires: []
artifacts:
  - research/artifacts/stw81-zero-dimensional-simple-field-audit-2026-08-30.md
---

A second-countable locally compact zero-dimensional space is strongly
zero-dimensional and paracompact.  Hence the open cover by bundle
trivialization charts has a countable pairwise-disjoint clopen refinement
`(U_k)_k`.  Restriction to these clopen pieces gives

`A ~= direct_sum_k^(c0) C_0(U_k) tensor B_k`,

where each `B_k` is a simple separable nuclear fibre.

Because `U_k` is second-countable and zero-dimensional, `C_0(U_k)` is AF.
Write it as an inductive limit of finite-dimensional commutative algebras.
After tensoring with `B_k`, every stage is a finite direct sum of copies of
`B_k`.  Inductive-limit permanence therefore gives

`dim_nuc(C_0(U_k) tensor B_k) <= dim_nuc(B_k)`.

Evaluation at any point of `U_k` is a quotient onto `B_k`, so quotient
monotonicity gives the reverse inequality.  Nuclear dimension of a
`c0`-direct sum is the supremum of the dimensions of its summands.  Thus

`dim_nuc(A)=sup_k dim_nuc(B_k)=sup_x dim_nuc(A_x)`.

The simple-algebra nuclear-dimension structure theorem says that every
simple separable fibre has nuclear dimension `0`, `1`, or `infinity`.
Taking a supremum of numbers in this set again gives `0`, `1`, or
`infinity`.

It remains to verify the shadow hypothesis rather than merely the desired
conclusion.  Since the fibres are nuclear and simple, ideals and quotients
of each trivial piece are obtained by restricting to open and closed
subsets of `U_k`.  Let `C` be a nonzero commutative hereditary subalgebra
of a quotient and let `J` be the ideal it generates.  Then `C` is full
hereditary in `J`, so `C` and `J` are strongly Morita equivalent.  In
particular, `J` is type I and `Prim(C)~=Prim(J)`.

On a piece with non-type-I simple fibre `B_k`, a nonzero `J` has a quotient
isomorphic to `B_k` by evaluation at a point of its support.  This is
impossible because quotients of type-I algebras are type I.  Hence `J` is
supported only on pieces whose simple fibre is elementary, necessarily
`K(H_k)`.  There `J` is a continuous-trace algebra over an open subset of
the zero-dimensional base.  Consequently `Prim(J)`, and therefore
`Prim(C)`, is zero-dimensional.
