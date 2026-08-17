---
rg: 2
id: leavitt-unit-group-has-no-finite-normal-subgroup
kind: claim
title: The binary Leavitt unit group has trivial center and no nontrivial finite normal subgroup
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies `R^x` with `GL_3 = EL_3` and proves it perfect; this uses that identification as an input and concludes something else entirely — that the group has no finite normal subgroup and no proper finite-index subgroup.
  leavitt-center-is-coefficient-field: that is the ring-side input, `Z(R) = F_2`, imported from the literature; this is the group-side conclusion drawn from it together with two formalized theorems, and it is what the primality criterion consumes.
  leavitt-unit-group-algebra-is-prime: that is the group-algebra consequence, reached from this one by Connell's criterion; this is a statement about the group and mentions no group algebra.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - GroupApproximation/Leavitt/ElementaryNoFiniteQuotients.lean
  - GroupApproximation/Leavitt/UnitAdditiveSpan.lean
---

Let `R = L_(F_2)(1,2)` and `G = R^x`.  Then

1. `G` has **no proper subgroup of finite index**;
2. `Z(G) = 1`;
3. every finite conjugacy class of `G` is a singleton, so `Delta(G) = 1`;
4. `G` has **no nontrivial finite normal subgroup**.

## Why each part

**(1)** `elementaryGroup_finite_quotient_trivial` says every homomorphism from
`EL_iota(R)` to a finite group is trivial, for an infinite ring with strong
two-sided division and at least three indices.  All three hypotheses are
formalized here — `LeavittFamily.infinite`,
`LeavittSimplicity.exists_mul_mul_eq_one`, and the three-leaf identification
`G ~= GL_3(R) = EL_3(R)` of `leavitt-gl-equals-el-and-perfect-unit-group`.  A
subgroup of index `n` would give a nontrivial action on its `n` cosets, hence
a nontrivial homomorphism to `S_n`.

**(2)** A central unit commutes with every unit of `R`, hence — by the
unit-span theorem `unitAdditiveSpan_eq_top`, which is what
`leavitt-unit-group-algebra-surjects-onto-leavitt` consumes — with every
element of `R`.  So `Z(G) = Z(R) n R^x`, and strong division makes every
nonzero central element a unit, so `Z(G) = Z(R)\{0}`.  By
`leavitt-center-is-coefficient-field` that is `{1}`.

**(3)** A finite conjugacy class means a centralizer of finite index, which by
(1) is all of `G`, which puts the element in `Z(G) = 1`.

**(4)** For `N` normal and finite, conjugation is a homomorphism
`G -> Aut(N)` with finite target, trivial by (1); so `N <= Z(G) = 1`.

## What this is for, and the one thing it is not

It is the group-side hypothesis of Connell's primality criterion, and its only
consumer is `leavitt-unit-group-algebra-is-prime`.

It is **not** a soficity or approximation statement, and it must not be read
as one.  `openai-leavitt-unit-nonsofic` announces that this group is not
sofic; part (1) says something in a different register — there is no residual
structure at all for that failure to hide behind.  The two are consistent and
neither implies the other.

Part (3) is the form actually consumed: `Delta(G) = 1` is all the Delta-method
version of the criterion needs, and it is a strictly stronger statement than
(4) here only in appearance — over this group they come from the same line.
