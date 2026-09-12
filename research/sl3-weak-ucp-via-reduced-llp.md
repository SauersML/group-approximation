---
rg: 2
id: sl3-weak-ucp-via-reduced-llp
kind: route
title: Dead — locally lift prescribed regular microstates through the reduced group C-star algebra
target: sl3-z-weakly-ucp-stable
requires: []
---

**Dead.**  A hyperlinear approximation with regular limiting character gives
a trace-preserving homomorphism from `C^*_r(SL_3(Z))` to a tracial matrix
ultraproduct.  The attempted shortcut was to invoke LLP of the reduced group
C-star algebra, lift that homomorphism on finite operator systems, and read
the coordinate ucp maps as the positive-definite corrections required by
weak ucp-stability.

The lifting premise is false: `sl3-reduced-group-cstar-has-no-llp` proves
that `C^*_r(SL_3(Z))` does not have LLP and carries the explicit
`invalidates` edge to this route.  Local reflexivity or exactness cannot be
substituted here; neither supplies ucp lifts through the tracial matrix
quotient.

This no-go does not decide the target.  Weak ucp-stability is formulated
through `C^*(SL_3(Z))` and asks for correction of each prescribed sequence,
so a sequence-specific rigidity theorem can still prove it even though both
the full and reduced LLP shortcuts fail.
