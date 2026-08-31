---
rg: 2
id: moved-root-dft-router-loses-quarter-and-collides-two-to-one
kind: claim
title: The moved-root DFT router is invertible on its orbit but retains only three eighths of the two-atom source
artifacts:
  - research/moved-root-dft-router-quarter-loss-proof.md
requires:
  - three-carrier-hidden-line-join-crosses-target-but-has-no-range
  - qutrit-head-preserving-scalar-router-is-three-cycle
distinct_from:
  three-carrier-hidden-line-join-crosses-target-but-has-no-range: that builds a full three-hidden-line source but has no nontrivial h transport; this moves through all three scalar types and computes the exact cost of the first h-typed Fourier router.
  qutrit-head-preserving-scalar-router-is-three-cycle: that uses one finite scalar permutation with complete Hecke graph; this uses literal S and T roots, collects their ST commutators, and diagonalizes the resulting relative holonomy.
---

Write the three nontrivial scalar types in `(k,h)` coordinates as

```text
M=W_2:(1,0),       D=W_1:(1,1),       O=W_0:(1,2).       (MDR1)
```

Thus the two raw block-root spaces

```text
U(A)=I+T A,      A in Hom(M,D),
V(B)=I+S B,      B in Hom(D,O)                         (MDR2)
```

each contain pure nonzero `h` weights. Their mixed commutator is

```text
[V(B),U(A)]=I+(ST)BA.                                  (MDR3)
```

For compatible rank-one `h` orbits, the nine composition coefficients
form the circulant matrix

```text
mathcal M =
[ 1 1 0
  0 1 1
  1 0 1 ].                                             (MDR4)
```

Over `C` its spectrum is

```text
2,                  1+omega,                  1+omega^2. (MDR5)
```

Hence `s_min(mathcal M)=1`. For the normalized orbit average
`mathcal M/3` the smallest singular value is exactly `1/3`. In
particular the moved-root cell has no Fourier zero; the literal proposal
`V_j=k^jVk^(-j)` was the wrong geometry because `C` is abelian and
cannot change the `h` weight of an `h`-neutral root.

The invertible incidence still does not give a Hall router. Put `p=ST`
and let

```text
L_0=Hom_(<k>)(M,O),             dim_(F_2)L_0=2,
N={I+p n:n in L_0}.                                      (MDR6)
```

Then `N isomorphic to C_2^2`, `k` fixes `N` pointwise, and `h` cycles
its three nonidentity elements. Every element of `N` is a product of
commutators in `(MDR3)`. If those elements are `r_0,r_1,r_2` in cyclic
order, define for `s=1,2`

```text
D_s=(1/2) sum_(j=0)^2 omega^(-sj)(r_j-1).                (MDR7)
```

With `p_N` the complement of the trivial-character projection of `N`,

```text
hD_sh^(-1)=omega^sD_s,       kD_sk^(-1)=D_s,
D_s^*D_s=D_sD_s^*=p_N,       tau(p_N)=3/4.              (MDR8)
```

The quarter loss is forced: every nontrivial `h`-weight in
`C[N]` vanishes on the trivial `N` character, and `D_s` is nonzero on
all other characters.

For the selected atoms `e_a=z_(1,a)`, the `h` exponents are
`2+a`. Therefore the collected modes themselves have the exact
full-`C` covariance

```text
D_2e_0=e_2D_2,                 D_1e_1=e_2D_1.            (MDR9)
```

Choose the three blocks in unused multiplicity copies, so the router
commutes with the three-line selector `X`. Let `f_t` denote the
`h`-character atom of exponent `t` and let `e_k` be the common
`k`-character atom in `e_0,e_1,e_2`. The correctly ordered two-source
row is

```text
mathcal T=D_2Xe_0+D_1Xe_1
         =(D_2f_2+D_1f_0)Xe_k.                          (MDR10)
```

It has range in the single `h` atom `f_1`. Its two branches have the
same final `N semidirect <h>` support, so their ranks do not add. Its
exact polar support rank is

```text
tau(supp abs(mathcal T)) =
  5/192       in the all-plus sign row,
  3/128       in every other surviving sign row.         (MDR11)
```

These are exactly `3/8` of the original two-atom ranks `5/72` and
`1/16`: a factor `3/4` from deleting the trivial `N` character and a
factor `1/2` from the two-to-one collision.

This is only an `h`-targeted row. The selector `X` is not
`k`-neutral, so `mathcal T` need not have range in the full atom
`e_2=f_1e_k`. The final target compression satisfies

```text
tau(supp abs(e_2 mathcal T)) <=
  5/192 or 3/128,                                      (MDR12)
```

and both bounds are strictly below `tau(Ee_2)=1/18`. Thus the first
corrected moved-root Fourier atlas is an exact firewall, not a
nonhyperlinearity witness. Proving that a `k`-typed component retains a
large source remains open.

The collected router and the finite sign packet lie in the finite group

```text
<N,C,H,C_1,W>,                 order 4*288=1152.          (MDR13)
```

Its regular representation realizes the quarter loss and the two-to-one
collision exactly. This finite absorber contains the collected
`ST` roots, not the uncollected raw `S` and `T` constituents. The live
next object is therefore a full-`C` Fourier occurrence in which a raw
constituent is retained through the final `k` range cut rather than
replaced by its finite commutator root.
