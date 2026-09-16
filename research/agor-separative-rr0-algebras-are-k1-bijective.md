---
rg: 2
id: agor-separative-rr0-algebras-are-k1-bijective
kind: claim
title: Separative unital real rank zero algebras are K1-bijective, and separativity is weak cancellation of all matrix algebras
distinct_from:
  stable-rank-one-unital-algebras-are-k1-bijective: that assumes stable rank one; this assumes separativity and real rank zero, which covers stable rank one and purely infinite simple algebras at once.
  stw99-problem-lx-rr0-weak-cancellation: that asks whether every real rank zero algebra is weakly cancellative and K1-surjective; this is the known conditional theorem that separativity gives both.
---

Let `A` be a unital complex C\*-algebra.

1. (AGOR Theorem 3.1.)  If `A` is separative and has real rank zero, the
   natural map `U(A)/U(A)° -> K_1(A)` is an isomorphism.
2. (AGOR, Section 3, remark before the Problem.)  `A` is separative, i.e.
   `p direct_sum p ~ p direct_sum q ~ q direct_sum q` implies `p ~ q` for
   projections `p, q` in `M_inf(A)`, if and only if every matrix algebra
   `M_n(A)` has Brown--Pedersen weak cancellation.

Weak cancellation, as recalled by Schafhauser--Tikuisis--White: projections
`p, q` generating the same closed ideal `I` with `[p]_0 = [q]_0` in `K_0(I)`
are equivalent.  STW also state that `A` is separative if and only if
`A tensor K` has weak cancellation.
