---
rg: 2
id: random-complex-stability-via-a3-cone
kind: route
title: Prove the random-complex cocycle stability rate with the A_3 metric cone
target: random-complex-linear-cocycle-stability
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - notes/TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md
---

The one place where this repository owns a tool that looks like the missing
input to `cocycle-stability-nonsofic-route`.  Chapman--Peled need, with high
probability in the middle density range `p = n^(-1+η)`, a permutation
cocycle-expansion bound

```text
h_1(Y, Sym) = ω(n^(-3) p^(-1)) = ω(n^(-2-η)),
```

and this corpus proves a dimension-free local repair theorem for
`Sym(d)`-valued connections on the spherical building `A_3(F_q)`, with the
constant `9` independent of everything.  The attack: transplant the
nine-triangle filling argument to the random complex, repair locally, and
assemble.

Dead: by `a3-cone-repairs-to-coboundaries-not-cocycles` the building estimate
measures distance to `B^1` and is available only because the cone is simply
connected, whereas the random-complex problem is about distance to `Z^1` on
complexes with nontrivial fundamental group — a repair to a pure gauge deletes
exactly the holonomy the estimate must retain.  The mismatch is structural,
not a matter of transporting the constant.

**What survives the demolition.**  The synchronization theorem itself, as a
local gadget and as the correct answer to the `d/2` fixity question; and the
observation that a genuine attack must patch local repairs *modulo an unknown
global cocycle*, which is what Chapman--Peled's expansion of connected covers
is designed to do.  The route that remains open is theirs
(`cocycle-stability-nonsofic-route`), and its hypothesis is untouched by
anything here.
