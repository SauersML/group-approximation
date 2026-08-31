---
rg: 2
id: two-native-singer-endpoint-gl6-proof
kind: route
title: Adjoin the first Singer block to the literal endpoint GL5 and generate all cross transvections
target: two-native-singers-and-endpoint-generate-literal-gl6
requires:
  - native-j1-extension-gives-gl5-but-only-second-whitehead-gram
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Use the ordered basis `(u_0,...,u_5)` of `(NSG1)`.  By
`native-j1-extension-gives-gl5-but-only-second-whitehead-gram`,

```text
H=<W,M_2,J_1>=GL(<u_1,...,u_5>)                       (1)
```

and `H` fixes `u_0`.  The first native Singer is supported on
`<u_0,u_1,u_2>`.  In this ordered triple, the exact native block calculation
gives

```text
       [1 1 0]                 [1 0 1]
g=M_1=[1 1 1],        g^(-1)= [0 0 1].                (2)
       [0 1 0]                 [1 1 0]
```

Write `t_ij=I+E_ij`.  All `t_ij` with distinct
`i,j in {1,...,5}` belong to `H`.  Direct conjugation using `(2)` gives

```text
g t_32 g^(-1)=t_30 t_31,
g t_13 g^(-1)=t_03 t_13 t_23.                         (3)
```

Indeed `g u_3=u_3` and `u_2^*g^(-1)=u_0^*+u_1^*`, proving the first
identity, while `g u_1=u_0+u_1+u_2` and
`u_3^*g^(-1)=u_3^*`, proving the second.  Hence

```text
t_30=(g t_32 g^(-1))t_31,
t_03=(g t_13 g^(-1))t_13t_23                         (4)
```

belong to `<H,g>`.  Conjugating `(4)` by the coordinate permutations in
`H` supplies every `t_i0` and `t_0j`, `1<=i,j<=5`.  Together with the
internal transvections in `H`, these are all elementary transvections on six
binary coordinates.  They generate `GL_6(F_2)=SL_6(F_2)`, proving the
image statement in `(NSG2)`.  Its order is

```text
product_(k=0)^5 (2^6-2^k)=20158709760.                (5)
```

For the literal lift, the Leavitt partial inverses used in the two native
three-summand blocks and in the endpoint Whitehead give a complete system of
projective matrix units on the six summands `(NSG1)`.  They therefore define
a homomorphism

```text
Phi:St_6(F_2) -> St_20(L_(F_2)(1,2)).                 (6)
```

Every generator in `(1)--(2)` lies in its image.  The elementary projection
of `Phi` is faithful on the displayed direct sum, and
`St_6(F_2)->SL_6(F_2)` has trivial finite-field Steinberg kernel.  Thus
`Phi` is injective on the generated subgroup and `(NSG2)` holds literally
upstairs.  Since the subgroup is all of this `GL_6(F_2)` block, the
individual elementary factors in `(NSG3)` belong to it as well.

Finally all displayed actors use only matrix indices `{2,4,5,7,8,9}`.
Ordinary disjoint-index Steinberg commutation therefore gives `(NSG4)`.
