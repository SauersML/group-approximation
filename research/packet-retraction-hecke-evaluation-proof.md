---
rg: 2
id: packet-retraction-hecke-evaluation-proof
kind: route
title: Apply the packet retraction entrywise in Morita coordinates
target: packet-retraction-evaluates-hecke-collision-atlas
requires:
  - primitive-packet-corner-is-matrix-over-hecke-atom
  - root-block-piecewise-transport-cannot-host-nonce-bcs
---

Linear extension of a group homomorphism is a star homomorphism of complex
group algebras.  Since the retraction fixes `K`, it fixes every packet
projection and is unital on its corner.  Applying it to all entries of an
algebraic projection atlas preserves every defining star identity and lands
in the finite root corner.  The root-block no-go excludes the result for the
fixed no-CE BCS, and the same argument excludes any strict finite-dimensional
gap instance.

For a primitive type, the rank-one atom corner maps to
`eC[K]e=Ce`.  Under the established Morita isomorphism, the corner map is
entrywise scalar evaluation `M_D(H)->M_D(Ce)`.  It preserves arbitrary
finite systems of matrix star-polynomial equations, in particular rank-two
collision-block and square-complex return equations.  Sending fresh group
letters to `1` gives exactly this map whenever the presentation retains the
packet retraction.  Therefore neither the number of cells nor a verified
`C(4)-T(4)` link can prevent the finite evaluation.  This proves the claim.

