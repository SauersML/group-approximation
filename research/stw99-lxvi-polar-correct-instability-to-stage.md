---
rg: 2
id: stw99-lxvi-polar-correct-instability-to-stage
kind: route
title: Approximate a proper limit isometry and preserve its norm-one defect
target: stw99-lxvi-injective-limits-cannot-create-instability
requires: []
---

Suppose the unit of `M_m(A)` is infinite, witnessed by an isometry `v` with
`vv*!=1`.  Its defect is a nonzero projection, so

```text
||1-vv*||=1.
```

Approximate `v` sufficiently closely by the image of an element
`x in M_m(A_n)` at some finite stage.  Then `x*x` is invertible, and polar
correction within that stage gives

```text
y=x(x*x)^(-1/2),         y*y=1.
```

By taking the initial approximation small enough, the image of `y` is within
less than `1/2` of `v`.  If `y` were unitary, then

```text
||1-vv*|| = ||yy*-vv*|| <= 2||y-v|| < 1,
```

contradicting the norm-one defect.  Thus `y` is a proper isometry in
`M_m(A_n)`.  This proves that matrix infiniteness of an injective limit is
already present at a finite stage.  It also proves that a limit of stably
finite stages is stably finite.

Now assume `A` itself is finite.  Every stage embeds unitally in `A`, so its
unit is finite.  Once one stage has an infinite matrix amplification, the
same proper isometry is carried injectively into every later stage.  Hence
the entire tail consists of finite but non-stably-finite algebras.
