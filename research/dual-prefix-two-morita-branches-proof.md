---
rg: 2
id: dual-prefix-two-morita-branches-proof
kind: route
title: Apply opposite one-sided Leavitt maps to adjacent Heisenberg roots
target: dual-prefix-growth-needs-two-morita-branches
requires: []
---

Additivity of the two one-sided coefficient maps proves all same-root rows
in `(DMB1)`.  For the mixed row,

```text
[iota_i(X(a)),iota_i(Y(b))]
 =Z((a t_i)(s_i b))
 =Z(a(t_i s_i)b)=Z(ab)=iota_i(Z(ab)),                  (DMP1)
```

so `iota_i` is a homomorphism.  It is injective: right multiplication by
`t_i` has left inverse right multiplication by `s_i`, and left
multiplication by `s_i` has left inverse left multiplication by `t_i`; the
center is fixed.  Equation `(DMB3)` is the off-diagonal Leavitt relation
`t_i s_j=0`.

Composition appends the matching `t` letters on the `X` side and the
reversed matching `s` letters on the `Y` side, proving `(DMB4)`.  For words
`u,v` of equal length,

```text
[iota_u(X(A)),iota_v(Y(A))]
 =Z(t_u s_v)=Z(delta_(u,v)A),                           (DMP2)
```

which is the complete dual-prefix table.  Each additional level takes the
central product of the two child packets and doubles symplectic rank.

By contrast, if `rho(P)` is one finite Pauli packet algebra and `U` is one
unitary, then `U rho(P) U^*` is isomorphic to `rho(P)`: conjugation preserves
its matrix-algebra dimension and alternating commutator rank.  No sequence
of conjugations of one packet, considered one at a time, grows rank.  The
growth in `(DMP2)` uses the union of two commuting conjugate images, not
automorphic transport itself.

Finally, `H(B)/Z(B)` contains the direct sum of the two additive root groups.
The pure prefixes make `B` infinite-dimensional over `F_p`, so this quotient
is not finitely generated and neither is `H(B)`.  A standard HNN extension
specifies an associated-subgroup map on a generating set; here that set is
necessarily infinite.  The only evident way to compress the edge relations
would be to extend `iota_i` to an endomorphism of the finitely presented
Steinberg ambient.  But a root-uniform ring endomorphism `theta` would have
to satisfy simultaneously

```text
theta(a)=a t_i,          theta(b)=s_i b,
```

and at `a=b=A` this says `theta(A)=t_i=s_i`, impossible by the Leavitt
grading.  Stabilized Morita conjugacy may transport each typed root corner,
but it remains rank-preserving on one transported packet and does not supply
the two commuting branch endomorphisms of the whole ambient group.

