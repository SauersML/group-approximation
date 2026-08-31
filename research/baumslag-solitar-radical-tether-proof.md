---
rg: 2
id: baumslag-solitar-radical-tether-proof
kind: route
title: Compute the MF reflection and the Bass--Serre action of the tether
target: baumslag-solitar-radical-tether-preserves-mf-reflection
requires:
  - universal-mf-quotient
---

Let

```text
B=<a,t | a t a^(-1)=t^2> ~= Z[1/2] semidirect Z,
```

where `a` acts on `Z[1/2]` by multiplication by `2`.  Since `d` has infinite
order,

```text
A=E *_(<d>=<a>) B.
```

The amalgam normal-form theorem embeds both vertex groups.  Every
finite-order element of an amalgam is conjugate into a vertex group; both
vertex groups are torsion-free, so `A` is torsion-free.  Eliminating `a`
gives the displayed finite presentation.

Write an element of `B` as `(r,k) in Z[1/2] semidirect Z`, with `a=(0,1)`
and `t=(1,0)`.  A direct calculation gives

```text
(r,k) a^n (r,k)^(-1)=((1-2^n)r,n).
```

For `n!=0` this lies in `<a>` only when `r=0`, i.e. only when
`(r,k) in <a>`.  Hence `<a>` is malnormal in `B`.  In the Bass--Serre tree
of `A`, two distinct edges incident to a `B`-vertex therefore have trivial
common stabilizer.  Every segment of length three contains such a pair, so
the tree action is 3-acylindrical.  The amalgam is reduced,
`[B:<a>]=infinity`, and `E!=<d>` (otherwise `E` would be infinite cyclic and
have trivial MF radical), so the action is non-elementary.  Thus `A` is
acylindrically hyperbolic.

Put `R=Rad_MF(E)`.  The map `p:A->E/R`, defined by `p(t)=1`, is well-defined
and its target is MF by `universal-mf-quotient`; hence

```text
Rad_MF(A) <= ker(p).                                  (1)
```

Conversely, let `Theta:A->U(Q)` be any norm-matrix-corona representation.
Its restriction to `E` kills `R`, hence kills `d`.  The tether relation gives

```text
Theta(t)=Theta(t)^2.
```

A unitary idempotent is the identity, so `Theta(t)=1`.  Therefore every
`Theta` factors through `p`, and `ker(p)<=Rad_MF(A)`.  Together with `(1)`
this proves equality and the quotient formula.  No spectral gap, Kazhdan
subgroup, or Property `(T)` occurs.
