---
rg: 2
id: radial-only-group-needs-a-cyclic-gcd-audit
kind: claim
title: The radial-only solution group needs an explicit cyclic gcd audit
distinct_from:
  radial-parallelograms-kill-simplex-class-two: that assumes the coordinate abelianization is the affine evaluation space W and kills its exterior square; this computes when the canonical radial-only presentation actually has that abelianization.
  four-local-parallelograms-are-minimal-simplex-operator-views: that identifies the local predicate accepted by every affine word; this distinguishes acceptance from the stronger assertion that the radial checks define exactly the affine code.
---

Let `K=F_(2^n)`, let `alpha` generate `K^*`, put

```text
gamma=alpha^b,
delta=1+alpha+gamma=alpha^c,
m=2^n-1,
f(z)=1+z+z^b+z^c in F_2[z].                          (RGA1)
```

The canonical radial-only homogeneous solution group is

```text
Gamma_rad=<q_i (i in Z/m) |
 q_i^2=1,
 [q_(i+u),q_(i+v)]=1       (u,v in {0,1,b,c}),
 q_i q_(i+1) q_(i+b) q_(i+c)=1>.                    (RGA2)
```

Its abelianization has dimension

```text
dim_F2 Gamma_rad^ab
 =deg gcd(f(z),z^m-1).                                (RGA3)
```

Indeed the abelianized relation module is the cyclic module
`F_2[z]/(z^m-1,f)`.  The affine evaluation code supplies an `(n+1)`-
dimensional quotient because `f(alpha)=f(1)=0`; equivalently the minimal
polynomial of `alpha` and `z+1` divide the gcd.  But equality with
`W=F_2 direct-sum K` requires the additional exact condition

```text
deg gcd(f,z^m-1)=n+1.                                 (RGA4)
```

Thus `radial-parallelograms-kill-simplex-class-two` is correct for an
underlying simplex presentation whose abelianization is already `W`, or for
a radial-only parameter set satisfying `(RGA4)`.  The phrase “the radial
homogeneous solution group” is otherwise ambiguous: accepting every affine
word does not prove there are no extra classical words, and extra
abelianization directions are not covered by the exterior-square argument
on `W`.

All conclusions below about the canonical radial-only group explicitly
assume `(RGA4)`.  This is a finite polynomial gcd check for each proposed
parameter family and should be recorded alongside the choice of
`alpha,gamma`.
