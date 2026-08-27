---
rg: 2
id: hull-quotients-are-not-word-hyperbolic-proof
kind: route
title: Read the conclusion of the theorem, and separate the two hyperbolicities
target: hull-quotients-are-not-word-hyperbolic
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - notes/HULL_ROUTING_AUDIT_2026-08-16.md
---

Two halves, neither of them deep; the node earns its place by being stated,
not by being hard.

**What the theorem concludes.**  Hull's small-cancellation theorem is stated
for a group acting acylindrically on a hyperbolic space, or equivalently for
an acylindrically hyperbolic group with a hyperbolically embedded subgroup,
and its quotients inherit that structure.  `notes/HULL_ROUTING_AUDIT_2026-08-16.md`
audits the published Theorem 7.1 field by field against this program's routing
package; word-hyperbolicity of the quotient appears in no field.  Where the
input is already word-hyperbolic and the relators are long enough, ordinary
hyperbolicity of the quotient is available — but that clause assumes what a
counterexample search would need to produce.

**Why the two cannot be conflated.**  Acylindrical hyperbolicity is
compatible with `ℤ^2` subgroups and with infinite normal subgroups of
infinite index; word-hyperbolicity is compatible with neither.  So no amount
of care with the relators converts an acylindrically hyperbolic output into a
word-hyperbolic one when the input already contains a `ℤ^2` — and the groups a
non-residual-finiteness route would want to push through Hull (the known
non-sofic examples, this program's lamp constructions) all do.
