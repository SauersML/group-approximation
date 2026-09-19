---
rg: 2
id: cuspidal-redistribution-orbit-basin-proof
kind: route
title: Redistribute equal Borel restrictions and use the congruence gap on the unmatched carrier
target: cuspidal-redistribution-refutes-regular-core-orbit-basin
requires:
  - regular-congruence-endpoint-orbit-has-uniform-selberg-retraction
---

Fix a prime `p=1 mod 4`, and write `G=PSL_2(F_p)`.  The standard character
table of `G` contains

```text
m=(p-1)/4                                                   (CRP1)
```

cuspidal irreducibles `delta_1,...,delta_m`, all of degree

```text
d_0=p-1.                                                    (CRP2)
```

Their characters have identical values on the standard Borel `P`: degree
`p-1` at the identity, zero on noncentral split semisimple elements, and
`-1` on nontrivial unipotent elements.  Equivalently,

```text
Res_P(delta_i)=Res_P(delta_j)       for all i,j.             (CRP3)
```

The image of the square-free BS core `B=<r,t>` is contained in `P`, so
`(CRP3)` remains true after restriction to `B`.

Let `rho` be the regular representation of `G`.  In its irreducible
decomposition, each `delta_i` occurs with multiplicity `d_0`.  Define an
exact representation `eta` by leaving every other irreducible multiplicity
unchanged and replacing the cuspidal multiplicity vector

```text
(d_0,d_0,...,d_0)
```

by

```text
(m d_0,0,...,0).                                          (CRP4)
```

The total dimension is unchanged.  Equation `(CRP3)` shows

```text
Res_B(eta) is unitarily equivalent to Res_B(rho).           (CRP5)
```

Conjugate `eta` once so that the two restrictions in `(CRP5)` agree
literally.  Both representations factor through the same exact congruence
quotient, so their square-free tuples obey all five presentation rows
exactly on the common core.

We next check the limiting character.  Let `g` be a fixed nonidentity
element of `A`.  For all sufficiently large `p`, its reduction `g_p` is
nonidentity.  The character difference is

```text
chi_eta(g_p)-chi_rho(g_p)
 =d_0(m chi_(delta_1)(g_p)-sum_i chi_(delta_i)(g_p)).       (CRP6)
```

It vanishes on split semisimple and unipotent elements by the common
character values above.  On a nonsplit semisimple element every cuspidal
character has the form `-(theta(z)+theta(z)^(-1))`, and hence absolute value
at most two.  Therefore the absolute value of `(CRP6)` is at most
`4m d_0=O(p^2)`.  Since

```text
|G|=p(p^2-1)/2=Theta(p^3),                                (CRP7)
```

the normalized character difference is `O(1/p)`.  The regular character
of `G`, pulled back to `A` along levels tending to infinity, converges
pointwise to the regular character of `A`.  The same is consequently true
of `eta`.

It remains to prove the orbit separation.  Let `H_rho,H_eta` be the two
representation spaces and put the normalized Hilbert--Schmidt norm on
`Hom(H_rho,H_eta)`.  For `a in A`, set

```text
beta(a)Z=eta(a) Z rho(a)^*.                                (CRP8)
```

The fixed vectors of `beta` are exactly the genuine `A`-intertwiners.  If
`U` is a unitary commuting with the common `B` action, then

```text
beta(b)U=U                         (b in B),
||beta(x)U-U||_2
 =||eta(x)-U rho(x)U^*||_2.                                (CRP9)
```

Apply the uniform congruence spectral gap `kappa` to `(CRP8)`.  Since all
the `B`-generator displacements in `(CRP9)` vanish,

```text
||eta(x)-U rho(x)U^*||_2
 >=kappa dist_2(U,Hom_A(H_rho,H_eta)).                      (CRP10)
```

For representations with irreducible multiplicities `(a_alpha)` and
`(b_alpha)`, the squared norm of the orthogonal projection of any unitary
onto the intertwiner space is at most

```text
(1/|G|) sum_alpha dim(alpha) min(a_alpha,b_alpha).          (CRP11)
```

Indeed, on the `alpha`-isotypic source and target carriers the diagonal
block of a unitary has squared Frobenius norm at most the smaller carrier
dimension; the off-isotypic blocks are orthogonal to every intertwiner.
All noncuspidal carriers in `rho,eta` agree.  Among the cuspidal carriers,
only the original `d_0` copies of `delta_1` can be common.  Hence `(CRP11)`
gives

```text
dist_2(U,Hom_A(H_rho,H_eta))^2
 >=((m-1)d_0^2)/|G|.                                     (CRP12)
```

Using `(CRP1)`, `(CRP2)` and `(CRP7)`, the right side tends to `1/2`.
Combining `(CRP10)` and `(CRP12)`, and then taking the infimum over every
`U in rho(B)'`, proves `(CRB4)` with, for example, any fixed
`c<kappa/sqrt(2)` for all sufficiently large `p`.

The same calculation explains why this is not a flexible-stability
counterexample.  The tuple `eta` is itself a genuine endpoint; only its
distance from the endpoint orbit having the regular finite-quotient
character is positive.
