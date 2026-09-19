---
rg: 2
id: binary-leavitt-all-ranks-full-mf-radical-proof
kind: route
title: Transport the rank-twelve MF black hole through prefix-code matrix self-similarity
target: binary-leavitt-all-ranks-full-mf-radical
requires:
  - rank-twelve-leavitt-simple-non-mf
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - GroupApproximation/Leavitt/PrefixCode.lean
  - GroupApproximation/KOne/AllRanksElementary.lean
  - non_mf_groups_exist.tex
---

For every `n>=1`, choose the complete left-comb binary prefix code

```text
C_n={1^j 0 : 0<=j<=n-2} union {1^(n-1)},
```

with the empty word used when `n=1`.  If `s_u,t_u` are the prefix products,
then

```text
t_u*s_v=delta_(u,v),       sum_(u in C_n) s_u*t_u=1.
```

Consequently

```text
Theta_n : M_n(R) -> R,
Theta_n((a_(u,v))) = sum_(u,v) s_u*a_(u,v)*t_v
```

is a ring isomorphism with inverse `r |-> (t_u*r*s_v)_(u,v)`.  Passing to
units gives

```text
GL_n(R) ~= R^x
```

for every positive `n`.

The all-ranks elementary-generation theorem gives `GL_n(R)=EL_n(R)` for
every `n>=2`.  In particular,

```text
R^x ~= GL_12(R)=EL_12(R).
```

The rank-twelve group on the right is nontrivial, finitely generated, simple,
Kazhdan, has full MF radical, and has no nontrivial finite-dimensional linear
representation over any field.  Each property is invariant under group
isomorphism, so it holds for `R^x`, every `GL_n(R)`, and every `EL_n(R)` with
`n>=2`.
