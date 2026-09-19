---
rg: 2
id: binary-leavitt-unit-group-fails-factorization-property
kind: claim
title: The binary Leavitt unit group fails Kirchberg's factorization property
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that asks whether the same explicit nonsofic group embeds into a tracial matrix ultraproduct; factorization is a strictly stronger ucp/microstate regularity property and may fail for hyperlinear Kazhdan groups.
  binary-leavitt-unit-group-has-tt-mod-t: that proves quasi-cocycle rigidity; this combines its property-T consequence with nonsoficity and Kirchberg's factorization theorem.
  openai-leavitt-unit-nonsofic: that excludes permutation models; this excludes the amenable-trace/factorization enhancement of unitary microstates.
---

Let

```text
L=L_(F_2)(1,2),              Q=L^x ~= EL_4(L).
```

Then `Q` does **not** have Kirchberg's factorization property.
Equivalently, the canonical trace on `C^*(Q)` is not an amenable trace.

This is a useful restriction on the unresolved fork
`binary-leavitt-unit-group-hyperlinear`.  If `Q` is hyperlinear, its
normalized-Hilbert--Schmidt models cannot be promoted to the ucp/factorizable
kind detected by Kirchberg's property.  Thus any positive hyperlinearity
construction for the first nonsofic group must live in the genuinely
non-factorizable matrix-ultraproduct sector.

The statement does **not** imply that `Q` is non-hyperlinear: hyperlinear
property-(T) groups without the factorization property are known.  Its role is
to remove a major false shortcut, not to identify the side of the fork.
