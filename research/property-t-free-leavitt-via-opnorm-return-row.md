---
rg: 2
id: property-t-free-leavitt-via-opnorm-return-row
kind: route
title: Authenticate one operator-norm coarse-to-fine row and cash the rank threshold, then saturate
target: property-t-free-leavitt-full-mf-radical
requires:
  - opnorm-leavitt-coarse-fine-return-row
  - authenticated-coarse-fine-return-forces-mf-collapse
  - full-leavitt-idempotent-defect-saturation
---

Suppose a norm-matrix-corona representation of the binary-Leavitt elementary
group keeps the distinguished root `z=x_13(q)` nontrivial.  Take unitary
coordinate lifts; the presentation is finite, so the relator defects
`Def_R(U_n)` tend to `0` in operator norm, and along a subsequence
`||z(U_n)-I||_op` is bounded below.

`opnorm-leavitt-coarse-fine-return-row` applies to exactly this data.  It
returns, at each such coordinate, a nonzero projection `P_n` carrying exact
depth-one (`M_2`) and depth-two (`M_4`) prefix matrix-unit systems with the
same identity, the coarse minimal corner `e_00`, its designated fine
descendant `f_(00,00)`, and the evaluated fixed three-elementary word
`J_x(U_n)`, with

```text
||(1-f_(00,00))J_x(U_n)e_00||_op <= omega(Def_R(U_n)) -> 0.
```

This is precisely the authenticated coarse-to-fine return of
`authenticated-coarse-fine-return-forces-mf-collapse` with `r=2`, `s=4`, mark
`z` and return word `J_x`.  That node's rank count -- `rank(e_00)` is half of
`rank(P_n)` and `rank(f_(00,00))` a quarter of it, so the row has operator
norm exactly `1` -- contradicts the display.

Hence every norm-corona representation kills `x_13(q)`, i.e.
`x_13(q) in Rad_MF(St_20(R))`.  By `full-leavitt-idempotent-defect-saturation`
the two Steinberg commutators

```text
[x_41(a t_1),x_13(q)]=x_43(a t_1 q),
[x_43(a t_1 q),x_32(s_1)]=x_42(a)
```

put one complete root subgroup inside `<<x_13(q)>>`, and the Weyl root
permutations put every root subgroup there, so `<<x_13(q)>>=St_20(R)`.  The
MF radical is normal, being an intersection of kernels, so

```text
Rad_MF(St_20(R))=St_20(R),
```

which is the goal.

**What this route buys over the two existing ones.**  The corona-module and
full-support-HS routes both pass through a positive-density active core and a
coefficient-module decoder.  This route needs neither: by
`rank-deficient-return-row-has-operator-norm-one` the obstruction threshold is
the rank threshold `1`, which is insensitive to carrier density and to
amplification, so the reblocking of
`torsion-normal-generator-has-full-support-corona-core` and the Hilbert-hotel
cancellation endpoints are not on the path at all.  It buys that at the price
of a strictly stronger row estimate, in the operator norm rather than the
normalized-HS norm; `opnorm-return-row-cannot-come-from-an-hs-ledger` records
that the price is real and that no existing 2-norm estimate can be reused to
pay it.  The three routes are therefore genuinely independent attacks on the
same goal, and the property-`(T)`-free character is common to all three.
