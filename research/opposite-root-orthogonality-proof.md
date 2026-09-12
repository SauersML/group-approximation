---
rg: 2
id: opposite-root-orthogonality-proof
kind: route
title: Expand both root-algebra factors and use their trivial intersection
target: opposite-root-orthogonality-charges-two-jump-gauges
requires: []
---

Write

```text
c=sum_(g in U) a_g lambda(g).
```

Then

```text
x c x=sum_(h in L) a_(x h x) lambda(h).
```

The coefficient of the identity in `c x c x` is a sum over pairs
`g in U,h in L` with `gh=1`.  Since `U intersect L={1}`, the only pair is
`g=h=1`.  Its coefficient is `a_1^2=tau(c)^2`, proving `(ORO1)`.
Equation `(ORO2)` is the unitary identity
`||z-1||_2^2=2-2 Re tau(z)`.

Put `a=tau(c)`.  Since `c` is unitary, `|a|<=1`.  If
`Re(a^2)<0`, `(ORO3)` is immediate because its right side squared is bigger
than two while the distance from a unitary to one of `+1,-1` is at most
two.  If `Re(a^2)>=0`, choose `sigma` with
`sigma Re(a)=|Re(a)|`.  Then

```text
||c-sigma||_2^2=2-2|Re(a)|.
```

Writing `a=p+iq`, one has `p^2 >= p^2-q^2=Re(a^2)`.  Hence
`|p|>=sqrt(Re(a^2))>=Re(a^2)`, and therefore

```text
2-2|p| <= 2-2 Re(a^2)=||(c x)^2-1||_2^2.
```

This proves `(ORO3)`.  The half-cycle gauge has equally many values `+1`
and `-1`, hence canonical trace zero, giving `(ORO4)`.

