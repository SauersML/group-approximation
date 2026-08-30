---
rg: 2
id: stw87-z2-boundary-freeness-and-limit-proof
kind: route
title: Partition along a cyclic coordinate and inspect every limit diagonal
target: stw87-z2-has-no-periodic-boundary-quotient
requires: []
---

## Stone--Cech freeness

Fix `0!=h in G`.  Choose a homomorphism `rho:G->Z` with `rho(h)!=0`, and
choose a prime `q` not dividing `rho(h)`.  The sets

```text
P_j={g in G:rho(g)=j mod q},             j in Z/qZ,
```

form a clopen partition of `beta G`, and translation by `h` permutes them
without fixing any member.  An ultrafilter selects exactly one member of a
finite partition.  If an ultrafilter `omega` were fixed by `h`, it would
have to select both `P_j` and the distinct translate `P_(j+rho(h))`, a
contradiction.  Hence every nonzero `h` acts freely.

A finite `G`-orbit would have a finite-index stabilizer and that stabilizer
would contain a nonzero element of `Z^2`, contradicting freeness.  Therefore
there is no nonempty finite invariant subset of `beta G`.

A unital star homomorphism

```text
q:C(beta G)->C(F)
```

is contravariantly a continuous map `F->beta G`.  If `q` is equivariant and
`F` is a nonempty finite `G`-set, the image of this map is a nonempty finite
invariant subset.  This is impossible.  Consequently the usual coefficient
quotient construction cannot produce a periodic crossed-product quotient
of `A`.

## No torus retraction

Suppose that `r:A->C*_r(G)` is a star homomorphism fixing every canonical
group unitary `lambda_g`.  Since `G` is abelian, covariance gives, for
`f in D`,

```text
r(alpha_g(f))
 = lambda_g r(f) lambda_g^*
 = r(f).
```

Composing `r|D` with evaluation at any point of `T^2` gives a unital
translation-invariant character of `D`.  Its Stone--Cech point would be
fixed by every translation, contradicting the first part.  Thus no such
homomorphic retraction exists.

## What limit operators actually retain

For `omega in beta G`, define the orbit map

```text
L_omega(f)(g)=f(g omega),                 f in C(beta G).
```

It is a unital equivariant star homomorphism `D->D`.  Since `G` is amenable,
the integrated covariant map defines a star homomorphism

```text
Phi_omega:A->A,
Phi_omega(f u_g)=L_omega(f)u_g.
```

It fixes all group unitaries.  If `omega` lies in the clopen closure of one
coset of a finite-index subgroup `H`, then `L_omega` permutes the
characteristic functions of the `H`-cosets.  Hence the range of `Phi_omega`
contains all of `C(G/H)` and all group unitaries, and therefore contains

```text
C(G/H) crossed_product_r G.
```

The transitive finite transformation groupoid identifies this algebra with
`M_k(C*_r(H))`, where `k=[G:H]`.  Since every finite-index subgroup of
`Z^2` is isomorphic to `Z^2`, this is `M_k(C(T^2))`.

For boundary `omega`, `L_omega` annihilates `c_0(G)`, so `Phi_omega` factors
through the uniform Roe corona; the periodic torus block nevertheless
survives in its image.  It is only a subalgebra, not a quotient or
hereditary corner.  Therefore neither its Bott class nor its nuclear
dimension supplies a lower bound for the ambient limit image or for `A`.

