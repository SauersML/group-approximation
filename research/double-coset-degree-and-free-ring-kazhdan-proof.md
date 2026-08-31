---
rg: 2
id: double-coset-degree-and-free-ring-kazhdan-proof
kind: route
title: Compute the raw-root Hecke edge and then use the two-generator ring
target: two-raw-roots-have-a-uniform-full-carrier-gap
requires:
  - constant-core-gap-stops-at-k-intertwiners
  - elementary-group-property-t-over-free-algebras
---

Write `e=E_ij` and `a=I+e tensor L`. Since `e^2=0` and the field has
characteristic two, `a^(-1)=a`. For `k in GL_m(F_2)`,

```text
a(k tensor I)a
 =k tensor I+(ek+ke) tensor L+(eke) tensor L^2.         (DCK1)
```

For `N=2` one has `L^2=0` and `I,L` are linearly independent. For
`N>=3` the matrices `I,L,L^2` are linearly independent. Thus the
expression in `(DCK1)` belongs to `K` only if `ek=ke`. Under that
condition `eke=ke^2=0`, so the condition is also sufficient. This proves
`(TRG1)`.

The right cosets in `KaK/K` are indexed by

```text
K/(K intersect aKa^(-1)).
```

The centralizer index of `e` is the size of the transvection conjugacy
class. Every transvection in `GL_m(F_2)` has the unique form
`I+u phi` with `u !=0`, `phi !=0`, and `phi(u)=0`. Hence

```text
[K:C_K(e)]
 =(2^m-1)(2^(m-1)-1),                                  (DCK2)
```

which proves `(TRG2)`.

Let `P_K` average the left `K`-action on `ell^2(F_N/K)`. The Hecke
compression

```text
H_L=P_K lambda(a_L) P_K
```

sends `delta_K` to the uniform vector on the `q` cosets in the orbit
`Ka_LK/K`, where `q` is the number in `(DCK2)`. In particular

```text
||H_L delta_K||^2=1/q,          <delta_K,H_Ldelta_K>=0. (DCK3)
```

Let `xi=d^(-1/2)sum_(gK)delta_(gK)` and

```text
v=(delta_K-d^(-1/2)xi)/sqrt(1-1/d).
```

Because `a_L notin K`, the two coset basis vectors `delta_K` and
`delta_(a_LK)` are orthogonal. The constant vector is invariant, so

```text
lambda(a_L)v-v
 =(delta_(a_LK)-delta_K)/sqrt(1-1/d).
```

This proves `(TRG3)`. The corresponding Hecke Rayleigh coefficient is

```text
<v,H_Lv>=-1/(d-1).                                     (DCK4)
```

It remains to control all K-fixed modes simultaneously. The two truncated
shifts generate the full matrix algebra. Indeed

```text
P_0=I-S_NT_N,
E_(r,s)=S_N^r P_0 T_N^s             (0<=r,s<N),         (DCK5)
```

where subtraction equals addition over `F_2`. Thus
`F_2<S_N,T_N>=M_N(F_2)`. Constant elementary conjugations move
`E_ij` through all root positions, root addition gives sums of
coefficients, and the Steinberg commutator

```text
[x_ij(b),x_jk(c)]=x_ik(bc)
```

gives products. Hence the constant roots together with the two raw roots
generate

```text
EL_m(M_N(F_2))=GL_(mN)(F_2)=F_N.                       (DCK6)
```

Finally take the property-T group

```text
Lambda=EL_m(F_2<s,t>)
```

and a fixed Kazhdan control set `Q` containing the constant and the two
free-root generators. The substitutions `s|->S_N` and `t|->T_N`,
together with `(DCK5)--(DCK6)`, give a quotient
`Lambda->F_N`. Property T descends to quotients, so the image `Q_N` has
one Kazhdan constant `kappa>0` for every `N`.

Apply this Kazhdan inequality to the unitary representation of `F_N` on
`Hom(H_1,H_0)`,

```text
q:T |-> pi_0(q)Tpi_1(q)^*.
```

Its invariant space is exactly `Hom_(F_N)(H_1,H_0)`. Multiplication on
the right by `pi_1(q)` converts displacement into
`||pi_0(q)T-Tpi_1(q)||_(HS)`, proving `(TRG4)`.

The spectral statement is therefore complete. What is not proved here is
that a nonlinear mixed-isotype Jacobson relator bounds each covariance
term in `(TRG4)`. Establishing that compiler, rather than improving the
Hecke gap, is the remaining step.
