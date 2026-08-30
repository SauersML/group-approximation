---
rg: 2
id: stable-lxxiii-multiplier-destabilization-proof
kind: route
title: Destabilize the fused nilpotent with a multiplier Cuntz pair
target: stable-algebras-solve-lxxiii
requires:
  - finite-square-zero-packet-covers-cutdown
  - finite-packets-fuse-after-one-stabilization
---

Put `h=(a-epsilon)_+`.  The finite-packet theorem gives square-zero
elements `x_1,...,x_n in A` such that

```text
h in I=Ideal(x_1)+...+Ideal(x_n).                    (1)
```

The one-stabilization fusion theorem then gives `W in M_2(A)` with

```text
W^2=0,
h tensor e_11 in Ideal_(M_2(A))(W).                  (2)
```

Because `A` is stable, its multiplier algebra contains isometries `s_1,s_2`
with

```text
s_i^*s_j=delta_(i,j)1,
s_1s_1^*+s_2s_2^*=1.                                (3)
```

They implement an isomorphism

```text
Theta:M_2(A)->A,
Theta((b_ij))=sum_(i,j=1)^2 s_i b_ij s_j^*.          (4)
```

Set `x=Theta(W)`.  Then `x^2=0`, and (2) gives

```text
s_1 h s_1^*=Theta(h tensor e_11) in Ideal_A(x)=J.    (5)
```

Every closed ideal of `A` is invariant under left and right multiplication
by elements of `M(A)`.  Multiplying (5) by `s_1^*` on the left and `s_1` on
the right therefore gives

```text
h=s_1^*(s_1 h s_1^*)s_1 in J.                       (6)
```

This proves the required ideal containment without asking the stable
isomorphism to fix every ideal globally.

For completeness, a stable algebra has no nonzero finite-dimensional
representation.  Such a representation would have a nonzero
finite-dimensional image, hence a nonzero finite-dimensional quotient of
`A`; stability passes to quotients, whereas a nonzero finite-dimensional
algebra cannot be isomorphic to its tensor product with `K`.
