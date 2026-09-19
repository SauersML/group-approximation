---
rg: 2
id: stw63-traceless-bidual-cu-collapse-proof
kind: route
title: Use full spectral cuts and proper infiniteness of the bidual
target: stw63-traceless-bidual-collapses-z-cu
requires: []
---

Put `M=B**`.  It has no nonzero finite central summand.  Indeed, if `zM`
were a nonzero finite summand, composing its center-valued trace with a
normal state of `Z(zM)` and restricting `b->zb` to `B` would give a tracial
state on `B`.  Hence `M`, and every `M_n(M)`, is properly infinite.

Fix `n` and nonzero `a in M_n(Z)_+`, and write `b=phi_n(a)`.  Choose
`0<t<||b||`.  The spectral cut `c=(b-t)_+` is the image of the nonzero
element `(a-t)_+` after slightly decreasing `t` if necessary.  Since
`M_n(Z)` is simple and the map is unital, `c` is norm-full in `M_n(B)`.
Consequently the spectral projection

```text
p=support(c)=1_(t,infinity)(b) in M_n(M)
```

is full with a finite fullness witness: for some finite `m`,

```text
1 is Murray--von Neumann subequivalent to p directSum ... directSum p
                                                    (m copies).       (2)
```

On every nonzero central compression, (2) prevents `p` from being finite,
because a finite direct sum of finite projections cannot dominate the
properly infinite central unit.  Thus `p` is a full properly infinite
projection.  It absorbs its finite amplification, so (2) improves to
`1<=p`; the reverse comparison is automatic.  Therefore `p~1`.

Since `b>=t p` on this cut-down spectral subspace, Cuntz comparison in
`M_n(M)`
gives

```text
[1]=[p] <= [b] <= [1].                                  (3)
```

Thus every nonzero class represented in a finite matrix algebra over `Z`
has the same image under (1).  In Robert's description
`Cu(Z)=N disjointUnion (0,infinity]`, every compact class and every finite
soft class has such a representative.  The infinite soft class is the
supremum of an increasing sequence of finite soft classes.  Cu-morphisms
preserve these suprema, so its image is the same class as well.

No step replaces `b` by its full support projection.  That replacement is
false for general positive elements of a von Neumann algebra.  The positive
lower bound `b>=tp` on the nonzero spectral cut is precisely what gives the
comparison `[p]<=[b]` used in (3).

The finite-fullness step is essential: proper infiniteness of the ambient
von Neumann algebra by itself would not justify equating projections of
different cardinal sizes.
