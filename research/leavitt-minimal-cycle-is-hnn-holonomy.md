---
rg: 2
id: leavitt-minimal-cycle-is-hnn-holonomy
kind: claim
title: Every same-orientation minimal carrier cycle is an HNN holonomy relation
artifacts:
  - research/leavitt-minimal-cycle-is-hnn-holonomy-proof.md
distinct_from:
  leavitt-omega-four-cycle-compiler: that gives one sufficient source-target quotient; this classifies every two-relator same-orientation four-cycle and identifies the exact coefficient holonomy which can collapse a coefficient copy.
  leavitt-d3-affine-two-carrier-transport-is-absent: that finite screen asks for two direct common-conjugator transports; this theorem exposes the broader one-holonomy mechanism which does not require either residual relator to be a transport word.
---

Let `D` be a coefficient group and suppose the two post-pivot residual
relators have the minimal carrier four-cycle form

```text
R0 = X A Y B,                 R1 = X C Y D,
```

where `A,B,C,D` are coefficient words and both occurrences of each carrier
have the displayed common orientation.  Reversible Tietze elimination of
`X` turns the quotient into

```text
<D,Y | Y^(-1) K Y = L>,
K=A^(-1)C,                    L=B D^(-1).
```

Thus the only coefficient obstruction carried by this minimal cycle is the
cyclic-subgroup holonomy `K -> L`.  If `K` and `L` have the same order, this
is an ordinary HNN extension and `D` embeds.  The Leavitt collapse requires
an order mismatch; the sharp choice is

```text
K=Omega(a,r)=1,               L=Omega(c,p)=h!=1.
```

Equivalently, the explicit residual template

```text
R0=X Y h,                     R1=X Omega(a,r) Y
```

kills `h` without either relator being a direct common-conjugator transport.
