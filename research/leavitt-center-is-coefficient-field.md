---
rg: 2
id: leavitt-center-is-coefficient-field
kind: claim
title: The center of the binary Leavitt algebra is its coefficient field
distinct_from:
  leavitt-unit-group-has-no-finite-normal-subgroup: that is the group-theoretic conclusion this claim is imported to reach, and it also consumes the no-finite-quotients theorem and the unit-span theorem; this is one ring-theoretic input to it, about `R` and not about `R^x`.
  binary-leavitt-algebra-not-directly-finite: that is the failure of direct finiteness in `R` itself, proved internally from the defining relations; this is a statement about the center of the same ring, imported, and the two share only their subject.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that is a soficity statement about the unit and elementary groups of d-ary Leavitt algebras over finite fields, proved here through property (T); this is a one-line ring fact about the center of the binary algebra over `F_2`, imported, and no approximation property appears in it.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies `GL_n(R)` with `EL_n(R)` and proves the unit group perfect, all internal; this says what the center of `R` is, is imported, and the only place they meet is as two separate inputs to the finite-normal-subgroup node.
  binary-leavitt-family-lifts-into-unit-corner: that asks for four elements of a group-algebra corner satisfying the Leavitt relations, and is open; this states what the center of the Leavitt algebra itself is, involves no group algebra and no corner, and is imported rather than open.
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

For a field `k`, the center of the Leavitt algebra `L_k(1,2)` is `k`.  In
particular

    Z(R) = F_2      for   R = L_(F_2)(1,2),

so `Z(R)^x = {1}`.

This is the center theorem for prime Leavitt path algebras applied to the
one-vertex two-loop graph, which is finite and satisfies Condition (L): for a
prime Leavitt path algebra the center is the coefficient field unless the
graph has a specific exceptional shape that this one does not have.

## What this repository has instead, and why that is not enough

`LeavittNormalForm.lean` proves that the monomials `s_alpha t_beta` **span**
`L_k(1,2)` as a `k`-vector space.  It does not prove they are linearly
independent, and no center computation is formalized here.  Spanning alone
does not decide the center: the computation that pins it down is a coefficient
argument in the monomial basis, and the basis is exactly the missing half.

Two fragments *are* internal, and they are the ones the downstream argument
uses most:

* `Z(R)` is a **field**.  Strong two-sided division
  (`LeavittSimplicity.exists_mul_mul_eq_one`: `a c b = 1` for every `c != 0`)
  turns into `c (ab) = (ab) c = 1` when `c` is central, so every nonzero
  central element is a unit and its inverse is central.
* `Z(R)` contains no element of order two, since `w^2 = 1` in characteristic
  two makes `w + 1` a central square-zero element, and a nonzero central
  element is a unit.

What remains, and what is imported, is that the field `Z(R)` is no larger than
`F_2` — equivalently, that `R` carries no central copy of `F_4`.  That is not
a formality: `R` does contain elements satisfying `x^2 + x + 1 = 0` (the
order-three unit `g` of `leavitt-corner-idempotent-unital-surjection` is one),
and the whole content of the import is that none of them is central.

## Scope

Used only through `leavitt-unit-group-has-no-finite-normal-subgroup`, to get
`Z(G) = 1` for `G = R^x`.  Nothing else in the graph depends on it.
