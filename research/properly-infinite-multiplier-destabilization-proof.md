---
rg: 2
id: properly-infinite-multiplier-destabilization-proof
kind: route
title: Destabilize the fused nilpotent with a multiplier Cuntz pair
target: properly-infinite-multiplier-solves-lxxiii
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

Proper infiniteness of `1_(M(A))` supplies isometries `s_1,s_2 in M(A)`
with

```text
s_i^*s_j=delta_(i,j)1.                               (3)
```

No assertion that their range projections sum to one is needed.  They give
an injective homomorphism into the range corner

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

This proves the required ideal containment even though the corner map (4)
need not be onto.

Finally, suppose `rho:A->M_n` is a nonzero finite-dimensional
representation and compress its codomain to the support of `rho`.  The
resulting nondegenerate representation extends unitally to `M(A)`.  Its
extension sends the two multiplier isometries to two isometries with
orthogonal ranges in a nonzero finite-dimensional corner, which is
impossible.  Thus the finite-dimensional-representation exclusion follows
from the multiplier hypothesis itself.  Stable algebras have properly
infinite multiplier unit, giving the first stated subclass.
