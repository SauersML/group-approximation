---
rg: 2
id: punctured-congruence-imprimitivity-is-only-flexibly-exact
kind: claim
title: Nested congruence PVMs can be asymptotically covariant but only flexibly exact
distinct_from:
  punctured-congruence-actions-are-inexact-on-every-fixed-level: that punctures the actor permutations themselves and repairs their multiplicativity by restoring one point; here the actor is an exact genuine congruence representation and the one-point seam lies only in every finite-orbit system of imprimitivity.
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that asks whether the full homogeneous-quotient crossed product has matrix microstates; this gives a finite-level near-genuine firewall and neither constructs nor excludes the denominator unitary.
  regular-congruence-depth-mixtures-remain-folner: that treats conductor-weight profiles and parahoric shift marginals; this shows that even a complete nested family of compact-level PVMs need not exactify in the original matrix dimensions.
---

Put

```text
C=SL_3(Z),                 Q_a=SL_3(Z/2^a Z),
d_a=|Q_a|+1,               sigma_a=lambda_(Q_a) direct_sum 1.       (PCI1)
```

Here `sigma_a` is pulled back along reduction `C -> Q_a`.  For every
`1<=j<=a` there is a `Q_j`-indexed PVM `(P_(a,j,y))_(y in Q_j)` on
`C^(d_a)` such that, for every fixed `c in C`,

```text
sum_(y in Q_j)
 ||sigma_a(c)P_(a,j,y)sigma_a(c)^*-P_(a,j,(c mod 2^j)y)||_2^2
 <=2/d_a.                                                        (PCI2)
```

The PVMs are compatible under every coarsening `Q_j -> Q_i`, `i<=j`, and
`sigma_a` has the canonical lattice character:

```text
tr_(d_a)(sigma_a(c))->0                 for every c!=1.            (PCI3)
```

Nevertheless, for no `j<=a` is there an exactly `sigma_a`-covariant
`Q_j`-indexed PVM in the same dimension.  Exact covariance over the
transitive `C`-set `Q_j` would force all atom ranks equal and therefore

```text
|Q_j| divides d_a=|Q_a|+1,                                      (PCI4)
```

which is impossible because `|Q_j|` divides `|Q_a|` and `|Q_j|>1`.

Deleting the one-dimensional trivial summand repairs **all** levels at
once: the regular summand carries the exact nested coset PVMs.  Thus the
finite compact-orbit data on a near-genuine homogeneous-quotient
microstate can at most force a FLEXIBLE system of imprimitivity without an
additional same-dimension rank argument.  It does not imply that the
coordinate representation is literally induced from every fixed principal
congruence subgroup, and it cannot by itself upgrade the one-level
isotypic-overlap or total-variation bounds to the whole scale-spread tower.

This is a firewall for an exactification inference, not a microstate for
`L^infinity(SL_3(Q_2)/Lambda') rtimes SL_3(Z[1/2])`: no denominator
operator or parahoric gluing relation is supplied.

The proof is `punctured-congruence-imprimitivity-proof`.
