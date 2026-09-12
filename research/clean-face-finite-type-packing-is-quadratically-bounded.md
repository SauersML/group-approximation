---
rg: 2
id: clean-face-finite-type-packing-is-quadratically-bounded
kind: claim
title: Orthogonal finite types attached through one clean face obey a quadratic packing bound
artifacts:
  - research/clean-face-restriction-bessel-packing-proof.md
distinct_from:
  finite-type-subprojection-forces-large-root-intersection: that bounds the root index for one transported type under the root carrier; this bounds how many such types can be mutually orthogonal when their atom groups meet through the same clean face.
  finite-type-additive-overlap-obeys-row-column-capacity: that bounds a many-to-many equality by row and column overlap capacities; this uses pairwise clean intersections and Bessel orthogonality to obstruct even the construction of one context partition.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that absorbs finite transport holonomy after a packet has been built; this prevents the central-face packet from being built in the first place at the maximal root index.
---

Let `K,A_1,...,A_n` be finite subgroups of a group `Gamma`, let

```text
pi in Irr(K),       alpha_a in Irr(A_a),
q=z_(K,pi),         p_a=z_(A_a,alpha_a),
d=dim(pi).
```

Assume that one finite subgroup `L` is a clean common face:

```text
K intersect A_a=L                         for every a,
A_a intersect A_b=L                       for a!=b.       (CFP1)
```

Suppose the `p_a` are nonzero mutually orthogonal subprojections of `q`:

```text
0!=p_a<=q,          p_a p_b=0 for a!=b.                 (CFP2)
```

Put

```text
s=[K:L],
r=<Res^K_L pi,Res^K_L pi>_L.                            (CFP3)
```

Then

```text
n s^2/d^2 <= r <= d^2.                                  (CFP4)
```

Equivalently,

```text
n <= d^2 r/s^2 <= d^4/s^2.                              (CFP5)
```

Thus two clean-face atoms already require

```text
[K:L]<=d^2/sqrt(2).                                     (CFP6)
```

At the extremal index allowed by
`finite-type-subprojection-forces-large-root-intersection`, namely
`[K:L]=d^2`, at most one atom can occur. In particular no nontrivial
partition

```text
q=sum_(a=1)^n p_a,             n>=2,                    (CFP7)
```

can be made from atom groups which all attach to the root and to one another
only through that face.

For an extraspecial Pauli root, `L=<J>` is the center,
`|K:L|=d^2`, and the unique spin type has dimension `d` and central sign
`J |-> -1`. Hence the tempting construction which attaches every finite
answer group cleanly along the central sign cannot produce even one
multi-atom context PVM. The transverse `D_8` cell shows the geometry behind
the obstruction: atoms from different maximal abelian charts meet only in
`<J>` and therefore overlap; orthogonal atoms in one basis share the whole
larger selector chart. A surviving finite-type incidence construction must
reuse extra selector isotropy between some atom groups, use non-clean
intersections, or leave the single-type syntax.
