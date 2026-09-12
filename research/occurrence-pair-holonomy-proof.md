---
rg: 2
id: occurrence-pair-holonomy-proof
kind: route
title: Fix one endpoint and count the possible simultaneous transports
target: two-transitive-occurrence-sections-have-unbounded-pair-holonomy
requires: []
---

Fix distinct base points `x_0,x_1`, sections `sigma_i` with
`sigma_i(x)x_i=x`, and a simultaneous transporter `g_(x,y)` for every
ordered pair `x!=y`.  Define

```text
h_0=sigma_0(x)^-1 g_(x,y) in Stab(x_0),
h_1=sigma_1(y)^-1 g_(x,y) in Stab(x_1).
```

Suppose both holonomies always lie in finite sets `B_0,B_1`.  Fix one
`x`.  From the two expressions for the transporter,

```text
sigma_1(y)=sigma_0(x)h_0(x,y)h_1(x,y)^-1
           in sigma_0(x)B_0B_1^-1.
```

The right side is finite.  Applying its elements to `x_1` permits only
finitely many values of `y`, contradicting the infinitude of the
two-transitive orbit.  Taking `B_i` to be intersections of the stabilizers
with ambient word balls proves unbounded ambient length.  Intrinsic
stabilizer balls give the same conclusion when those stabilizers are
finitely generated.

For occurrence operators, conjugating the prototype by `g_(x,y)` and
comparing it with the section-named endpoint inserts exactly `h_i`; hence
the group-theoretic statement directly yields the claimed compiler
obstruction.
