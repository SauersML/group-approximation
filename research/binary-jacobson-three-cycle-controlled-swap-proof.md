---
rg: 2
id: binary-jacobson-three-cycle-controlled-swap-proof
kind: route
title: Multiply the three triangular rows and isolate the common-column amenable extension
target: binary-jacobson-three-cycle-is-controlled-swap-and-marked-mf
requires:
  - binary-jacobson-monomial-symbol-preimage-is-marked-mf
  - amenable-implies-operator-mf
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
---

Write the three matrices in the standard row order `(1,2,3)`:

```text
a_12=[[S,Q,0],[0,T,0],[0,0,1]],
a_23=[[1,0,0],[0,S,Q],[0,0,T]],
a_31=[[T,0,0],[0,1,0],[Q,0,S]].                         (JTCP1)
```

The inverse formula in `(JTC1)` follows from

```text
TS=1,       TQ=0,       QS=0,       Q^2=Q,
ST+Q=1.                                                    (JTCP2)
```

Left multiplication of a coefficient column by `(JTCP1)` gives `(JTC2)`;
the corresponding root factors commute because they have a common target
index and distinct source indices.

Direct multiplication gives

```text
a_23 a_12=[[S,Q,0],[0,ST,Q],[0,0,T]],
a_31 a_23 a_12
 =[[TS,TQ,0],[0,ST,Q],[QS,Q^2,ST]]
 =[[1,0,0],[0,P,Q],[0,Q,P]].                            (JTCP3)
```

Here `P=ST` and `Q=1-P` are complementary orthogonal idempotents.  Squaring
the lower block in `(JTCP3)` gives

```text
[[P,Q],[Q,P]]^2=[[P+Q,0],[0,P+Q]]=1,                   (JTCP4)
```

so `c^2=1`.  Applying `(JTCP3)` to the coefficient columns `(0,1,0)^t`,
`(0,0,1)^t`, `(0,Q,0)^t`, and `(0,0,Q)^t` gives `(JTC4)`.  In characteristic
two,

```text
x_24(P)=x_24(1+Q)=u_2 z_2.
```

All four roots `u_2,u_3,z_2,z_3` commute and are involutions.  Their
coefficients are linearly independent in their respective root positions:
`Q` is neither `0` nor `1` in `J` (for example in the standard unilateral
shift representation), so the generated root subgroup is `C_2^4` and
contains the nontrivial element `z_2`.  Equations `(JTC4)` show it is
normalized by `c,w_23`.  The matrices `c` and `w_23` commute: on the
`P`-corner `c` is the identity and on the `Q`-corner it is the same swap as
`w_23`.  Thus `H` is finite (indeed a quotient of `C_2^4 semidirect C_2^2`),
and its regular representation retains `z_2`.

For the full three-shift subsystem, each `a_ij` has Laurent symbol equal to
the diagonal monomial with entries `z,z^(-1)` in positions `i,j`, and the
Weyl word `w_23` has a determinant-one monomial symbol (over `F_2` the sign
is trivial).  Hence `A<=K`.  The cited monomial-preimage theorem says `K` is
amenable, so `A` is amenable.

The Steinberg relations show directly that `U_4` is abelian.  Conjugation by
an element supported on the first three coordinate rows left-multiplies the
coefficient column and hence preserves `U_4`; therefore `U_4` is normalized
by `A`.  It follows that `G_triangle cap U_4` is an abelian normal subgroup
and that the natural image of `G_triangle` modulo it is a quotient of `A`.
Amenability is closed under extensions, so `G_triangle` is amenable.  Its
inclusion in `E` keeps `z_2` nontrivial, and
`amenable-implies-operator-mf` supplies the faithful norm-corona model.
