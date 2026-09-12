---
rg: 2
id: stw99-lxxvi-one-dim-nccw-s6-criterion
kind: claim
title: The zero-skeleton dimension vector exactly decides S6 scalar survival in every one-dimensional NCCW block
distinct_from:
  stw99-lxxvi-dimension-drop-subalgebra-kills-s6-class: that treats the two-endpoint generalized dimension-drop block; this gives a necessary-and-sufficient criterion for arbitrary finite-dimensional endpoint multiplicity matrices and any number of summands.
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let

```text
E=directSum_(i=1)^s M_(r_i),
F=directSum_(j=1)^t M_(d_j),
```

and let `phi_0,phi_1:E->F` be unital star homomorphisms.  Write their
endpoint multiplicity matrices as

```text
mu_epsilon=(m_(epsilon,j,i)),
d_j=sum_i m_(epsilon,j,i) r_i       (epsilon=0,1).      (M)
```

Form the unital one-dimensional NCCW pullback

```text
A={ (f,a) in C([0,1],F) directSum E:
     f(0)=phi_0(a), f(1)=phi_1(a) }.
```

For the nonzero class `alpha in pi_5(U(2))=Z/2`, the scalar image

```text
alpha_A in pi_5(U(M_2(A)))
```

vanishes if and only if

```text
r_i>=2 for every zero-skeleton summand i.               (NCCW)
```

Thus `(NCCW)` is an exact computable criterion from the finite NCCW data:
there may be arbitrary numbers of summands and arbitrary endpoint
multiplicity matrices satisfying `(M)`; the only obstruction is a column
whose source block has size one.  No parity, determinant, or difference
condition on `mu_0-mu_1` remains in degree five.

Consequently, if a unital C*-algebra `D` contains a unital copy of any such
one-dimensional NCCW block satisfying `(NCCW)`, then the scalar image of
`alpha` is zero in `pi_5(U(M_2(D)))`.  A coefficient for the surviving `S^6`
route can therefore contain no unital one-dimensional NCCW block whose
zero-skeleton has no characters.

This strictly broadens the dimension-drop no-go: generalized
`I_(p,q)` is the two-vertex special case, whereas the theorem permits
arbitrary multi-summand zero- and one-skeleta and arbitrary endpoint
multiplicities.  Conversely, if even one `C` summand occurs in `E`, the
scalar class survives in `A`, regardless of how strongly that summand is
amplified or mixed at the two endpoints.
