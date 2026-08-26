---
rg: 2
id: kt-finitary-outerity-support-proof
kind: route
title: Move Laurent coefficients through infinitely many negative cones and isolate the constant scalar kernel
target: kt-finitary-action-is-outer-mod-scalar-core
requires:
  - kun-thom-nonsofic-wreath
  - wreath-candidate-embeds-in-finitary-permutation-extension
---

Write `E=EL_r(F_q[x_1^(+-1),x_2^(+-1),x_3^(+-1)])`, so
`G=E rtimes SL_3(Z)`, and let `pr:G->SL_3(Z)` be the quotient map.  Since
`Gamma<=ker(pr)`, if `g=(e,L)` has `L!=1`, then for every `y in G`

```text
pr(y^(-1) g y)=pr(y)^(-1)L pr(y)!=1.
```

Thus `y^(-1)gy notin Gamma`: such a `g` fixes no coset at all.

It remains to take `e in E`.  If some matrix entry of `e` contains a Laurent
monomial with nonzero exponent `v in Z^3`, choose infinitely many
`L_n in SL_3(Z)` sending `v` to vectors with a negative coordinate.  One
explicit construction first sends `v` to `(d,0,0)`, where `d` is the gcd of
its coordinates, and then applies the shears

```text
[[1,0,0],[-n,1,0],[0,0,1]].
```

Monomial substitution is injective on the exponent lattice, so the selected
coefficient cannot cancel.  Hence `L_n^(-1)eL_n` has a nonpolynomial entry
and is not in `Gamma`.  The cosets `L_n Gamma` are distinct by their external
`SL_3(Z)` projections, so `e` moves infinitely many cosets.

Suppose instead that `e` is a constant nonscalar matrix.  Some matrix unit
`E_ij` does not commute with `e`.  For

```text
y_n=I+x_1^(-n)E_ij
```

one has

```text
y_n^(-1)e y_n
 =e+x_1^(-n)(eE_ij-E_ij e)-x_1^(-2n)E_ij e E_ij.       (1)
```

The coefficient at degree `-n` is nonzero and cannot cancel with the degree
`-2n` term, so `(1)` is outside `Gamma`.  Moreover
`y_m^(-1)y_n=I+(x_1^(-n)-x_1^(-m))E_ij` is outside `Gamma` for `m!=n`, so
these are infinitely many distinct moved cosets.

The remaining constant matrices commute with every matrix unit and are
therefore scalar.  A scalar Laurent unit of determinant one is exactly
`zeta I_r` with `zeta^r=1`; these elements are fixed by monomial substitution
and central in `E`, hence in `G`, and lie in `Gamma`.  They act trivially on
`G/Gamma`.  This proves `(OUT1)` and the infinite-support assertion.

Item 4 of `wreath-candidate-embeds-in-finitary-permutation-extension` says
that every infinite-support permutation of `Y` induces an outer automorphism
of `L(Sym_fin(Y))`, proving `(OUT2)`.  Over `F_2` the multiplicative group is
trivial, so `Z_0={1}`.
