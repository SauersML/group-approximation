---
rg: 2
id: stw22-colour-intrinsic-local-replications-proof
kind: route
title: Colour independently chosen local replication tuples
target: stw22-intrinsic-local-replication-colouring-reduction
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-positive-dimensional-intrinsic-selection-frontier-audit-2026-08-30.md
---

We first prove `(ILR3)`.  Cover the specified closed set outside which `a`
vanishes by finitely many open sets on which `(ILR2)` holds.  The
covering-dimension refinement
theorem gives a finite subordinate refinement `(U_alpha)` which is the
union of `d+1` families, with the members of each family pairwise discrete.
By normality, shrink the refinement so that the closure of each member still
lies inside an ILR neighbourhood. Choose a partition of unity `(f_alpha)`
on the closed set, extend it over a neighbourhood, and choose the extensions
with compact support inside the corresponding shrunken members. Thus their
supports remain pairwise disjoint within each colour. After multiplying by
a central cutoff which is one on the closed set, we may regard the
`f_alpha` as elements of `C(K)_+` satisfying

```text
sum_alpha f_alpha=1       wherever a is nonzero.        (ILR4)
```

For each `alpha`, choose a local tuple
`w_(1,alpha),...,w_(m,alpha)` furnished by `(ILR2)` on a neighbourhood of
`supp(f_alpha)`.  For `0<=r<=d`, put

```text
v_(j,r)=sum_(colour(alpha)=r) f_alpha^(1/2)w_(j,alpha). (ILR5)
```

The sum is an element of `M`.  Same-colour scalar supports are disjoint, so
all cross terms in `(ILR5)` vanish.  Equations `(ILR2)` and `(ILR4)` give

```text
sum_(r=0)^d v_(j,r)^*v_(j,r)
 =sum_alpha f_alpha a=a.                               (ILR6)
```

Fix a fibre and a colour.  At most one `alpha` of that colour is active.
Inside its local tuple, the positive contractions
`w_(j,alpha)w_(j,alpha)^*` are pairwise orthogonal.  Their sum is therefore
a positive contraction.  Consequently

```text
norm(sum_(j=1)^m v_(j,r)v_(j,r)^*)<=1,
norm(sum_(r=0)^d sum_(j=1)^m v_(j,r)v_(j,r)^*)<=d+1.   (ILR7)
```

This proves `(ILR3)`.  Notice that range elements belonging to different
patches are never compared: disjointness handles patches of one colour,
and the norm estimate simply adds the `d+1` colours.  Thus neither global
comparison projections nor transition maps occur.

Now fix `x in K`, let `0<=b<=1` belong to the `2`-null ideal `K_x`, and
fix `epsilon>0` and `m>=1`.  Put `c=(b-epsilon)_+`.  Since
`tau_x(b^2)=0` and `y |-> tau_y(b^2)` is continuous, Chebyshev's inequality
gives a neighbourhood `V` of `x` on which

```text
tau_y(supp(c_y))<1/(2m).                                (ILR8)
```

Choose `h in C(K)_+` equal to one on a neighbourhood of `x`, with closed
support contained in `V`, and set `a=hc`.  Then `[a]=[c]` in `K_x/J_x`,
and `(ILR1)` holds.  Apply `(ILR3)`.  Equation `(ILR6)` implies that every
`v_(j,r)` belongs to `K_x`.  If `sigma` is a bounded positive trace on the
gap, traciality and `(ILR7)` give

```text
m sigma([c])
 =sum_(j,r) sigma([v_(j,r)^*v_(j,r)])
 =sigma(sum_(j,r)[v_(j,r)v_(j,r)^*])
 <=(d+1)||sigma||.                                     (ILR9)
```

The integer `m` is arbitrary, hence `sigma([c])=0`.  Letting `epsilon`
decrease to zero shows that `sigma([b])=0`.  Thus every fibre gap is
bounded-trace-free, and
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` gives the claimed
description and uniform continuity of all traces.
