---
rg: 2
id: binary-leavitt-factorization-failure-proof
kind: route
title: Combine nonsoficity, property T, and Kirchberg's residual-finiteness theorem
target: binary-leavitt-unit-group-fails-factorization-property
requires:
  - binary-leavitt-unit-group-has-tt-mod-t
  - openai-leavitt-unit-nonsofic
---

Write `Q=L_(F_2)(1,2)^x`.  By
`binary-leavitt-unit-group-has-tt-mod-t`, `Q` has property `(TT)/T`, hence in
particular Kazhdan's property `(T)`.  By `openai-leavitt-unit-nonsofic`, `Q`
is not sofic.  Every residually finite group is sofic (indeed LEF), so `Q` is
not residually finite.

Kirchberg's 1994 theorem states that a discrete group with property `(T)` and
the factorization property is residually finite.  Applying the contrapositive
to `Q` gives

```text
property (T) + not residually finite
    => not factorization property.
```

Hence `Q` fails Kirchberg's factorization property.  Using Kirchberg's
amenable-trace characterization, this is equivalently failure of amenability
of the canonical trace on `C^*(Q)`.

The conclusion is intentionally weaker than non-hyperlinearity.  The
factorization property supplies ucp matrix approximants, while hyperlinearity
only supplies normalized-HS group microstates; property `(T)` does not bridge
that gap without an additional lifting/stability input.
