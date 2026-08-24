---
rg: 2
id: leavitt-unit-internal-shift-proof
kind: route
title: Shift a bilateral antichain of Leavitt cylinders with one prefix-table unit
target: leavitt-unit-internal-shift-reflection
requires:
  - binary-leavitt-all-ranks-full-mf-radical
artifacts:
  - GroupApproximation/Leavitt/PrefixCode.lean
---

Put `R=L_(F_2)(1,2)` and `U=R^x`.  Consider the complete prefix-code
bijection

```text
0  |-> 00,
10 |-> 01,
11 |-> 1.
```

Its prefix-table unit is

```text
v=s_00 t_0+s_01 t_10+s_1 t_11.                          (ISP1)
```

The inverse is obtained by reversing the three arrows.  Define a bilateral
family of words by

```text
w_0=10,
w_i=0^i 1                    if i>=1,
w_(-k)=1^(k+1) 0             if k>=1.                   (ISP2)
```

These words are pairwise prefix-incomparable.  The prefix table gives

```text
v s_(w_i)t_(w_i) v^(-1)=s_(w_(i+1))t_(w_(i+1))          (ISP3)
```

for every integer `i`: it sends `10` to `01`, adds one leading zero on the
positive ray, removes one leading one on the negative ray, and sends `110`
to `10`.

Put `p_i=s_(w_i)t_(w_i)`.  For a finitely supported tuple
`g=(g_i) in U^(Z)`, define

```text
beta(g)=1+sum_i s_(w_i)(g_i-1)t_(w_i).                  (ISP4)
```

Prefix orthogonality makes `beta` an injective homomorphism and gives
`beta(g)^(-1)=beta(g^(-1))`.  Equation `(ISP3)` gives

```text
v beta((g_i)) v^(-1)=beta((g_(i-1))).                   (ISP5)
```

The element `v` has infinite order because it translates the pairwise
distinct projections `p_i`.  Moreover, `beta(U^(Z))` fixes every `p_i`, so
no nonzero power of `v` belongs to the base.  Equations `(ISP4)`--`(ISP5)`
therefore give the injective semidirect-product map `(IS1)`.

The group `U` is finitely generated.  A finite generating set in coordinate
zero together with `v` generates `W_Z`, since conjugation by powers of `v`
reaches every coordinate.

Every MF-target homomorphism kills every coordinate copy of `U`, so it kills
the base and factors uniquely through the height map to `Z`.  The group `Z`
is MF, hence the height map detects every element outside the base and proves
`(IS2)`.  The identical factorization applies to the other target classes in
the claim because every map from `U` to such a target is trivial.

Choose a nonidentity involution `d in U` and place it in coordinate zero.
Simplicity of `U` and translation by `v` show that its normal closure is the
whole base.  If `N` is normal in `W_Z`, all MF-target maps killing `N`
correspond to MF-target maps from `Z` killing the image of `N`.  Every
quotient of `Z` is MF, so pulling its exact closure back along the height map
gives `(IS3)` and `(IS4)`.
