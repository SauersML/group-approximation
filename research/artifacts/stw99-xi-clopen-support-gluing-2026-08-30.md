---
title: STW XI checkpoint --- compact-open support exhaustions force quasidiagonal extensions (2026-08-30)
---

## The new permanence theorem

For an invariant closed subset `Y` of a compact `Z^d`-space `X`, put
`U=X\Y`.  If `U` is exhausted by increasing invariant compact-open sets
`K_n`, then the projections `1_(K_n)` are central in
`C(X) rtimes Z^d` and form an approximate unit for the ideal
`C_0(U) rtimes Z^d`.  Their corners are exactly

`C(K_n) rtimes Z^d`.

Consequently, quasidiagonality of every compact support corner and of the
closed-support quotient `C(Y) rtimes Z^d` implies quasidiagonality of the
whole crossed product.  Iterating gives the same result for finite chains
of invariant closed supports whose successive open strata admit
compact-open invariant exhaustions.

There is a direct mixed corollary.  If the whole crossed product is stably
finite, the open-stratum ideal is traceless, and the closed subsystem `Y`
has a full-support invariant probability measure, then the whole crossed
product is quasidiagonal.  Gabe makes the stably finite traceless ideal
AF-embeddable; the faithful-trace UCT theorem makes the quotient
AF-embeddable; and the central cuts glue their quasidiagonal models.  In
fact every bounded trace on the whole algebra kills the traceless ideal, so
when that ideal is nonzero there is no global faithful trace.  The quotient
trace prevents the whole algebra from being traceless.  Thus this really
lies between the two previously solved global regimes.

This is a genuine dynamical extension mechanism: the topological exhaustion
manufactures a central projectional approximate unit, the extra ingredient
missing from an arbitrary extension.  The proof then invokes the repository's
abstract two-cut theorem
`stw09-local-mf-corner-traces-across-qd-extension-force-qd`.

## How it advances the XI reduction

The earlier trace-support reduction left quasidiagonality to be glued across
extensions between measured-support and traceless strata.  The theorem
closes precisely those finite filtration steps for which the intervening
open stratum is zero-dimensional in the strong equivariant sense above.
The hypotheses on the pieces can be discharged by any available method.
The mixed corollary is the canonical example: the closed quotient uses its
faithful invariant measure, while the nonunital open ideal uses Gabe's
traceless theorem.

No AF-embedding conclusion is claimed.  The coordinate cuts prove
quasidiagonality of the extension, but turning an arbitrary exact
quasidiagonal algebra into an AF subalgebra is STW Problem VIII.  Keeping
this boundary explicit prevents the support filtration from silently
assuming the other open problem.
