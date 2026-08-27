---
rg: 2
id: leavitt-two-relator-corner-peeling
kind: claim
title: A post-pivot Leavitt consequence needs a nonempty long-corner two-core
artifacts:
  - research/leavitt-two-relator-corner-peeling-proof.md
distinct_from:
  leavitt-degree3-direct-pivot-screen-is-empty: that enumerates literal Bergman reductions of the fixed packet; this is an abstract Tietze criterion for genuinely joint use of the second unary relator.
---

Let `D` be a group, let `Q=D*F(X)`, and impose finitely many relators over
`Q`.  Repeatedly delete a relator containing a free letter which occurs
exactly once, with exponent `+1` or `-1`, in the entire remaining relator
family, and delete that letter too.  If this peeling deletes every relator,
then the quotient is `D*F(X_0)` for the undeleted letters.  In particular the
map from `D` is injective.

Consequently, after one unary orbit of a degree-three cyclic cover is used to
eliminate the stable letter, the second unary orbit and the nine-valent orbit
can kill the marked element `h=[c,d]` of

```text
D=V4(a,b)*D8(c,d)
```

only if their long-corner incidence has a nonempty two-core.  The smallest
two-relator incidence with no initial singleton is the four-incidence cycle

```text
<D,H,Y | Y H^(-1), Y h H^(-1)>.
```

Both long letters have incidence degree two, and eliminating the first
relator changes the second to `H h H^(-1)`, so this abstract presentation
does kill `h`.  Thus a search for a joint two-orbit consequence should look
for a long-corner cycle; another freely occurring tail cannot work.
