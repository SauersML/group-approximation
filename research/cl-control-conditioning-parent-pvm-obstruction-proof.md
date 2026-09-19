---
rg: 2
id: cl-control-conditioning-parent-pvm-obstruction-proof
kind: route
title: Separate fixed-fiber narrowing, distribution conditioning, and public control revelation
target: revealing-cl-controls-breaks-compression
requires:
  - jnvwy-perfect-introspection-forces-full-seed-support
---

Fixing the successive classical controls of a JNVWY conditionally linear map
makes its restriction affine.  This algebraic observation does not yield an
upstream affine-profile compiler.

First retain the original introspection questions and narrow `SAMPLE` answers
to one proper control fiber.  The exact Pauli acceptance equations, tracial
conjugacy of the Pauli-Z atoms, and exact Pauli--Sample consistency make the
marginalized `SAMPLE` seed distribution uniform in every perfect model.  A
fiber fixing `r` independent control bits therefore has state mass `2^(-r)`,
so a test accepting only that fiber cannot be passed perfectly.

Second condition the source seed distribution on the fiber.  This preserves a
perfect source strategy, but it is not soundness monotone: different
conditional branches may use incompatible measurements.  CHSH conditioned on
one question pair is the elementary counterexample to any general implication
from branch soundness to soundness of the mixture.

Third send the control as a new premeasurement question.  This permits a
different PVM in every fiber, whereas the JNVWY decoder uses one parent
`SAMPLE` PVM and its `INTRO` coarse-grainings in equations (79)--(80).
Forgetting the control only gives a POVM in general.  Requiring literal common-
parent coherence makes each branch sum to its proper fiber projection rather
than the identity and restores the first obstruction.  Thus a public-control
repair requires a new coherent conditioned-introspection theorem.  Moreover,
after anchored repetition, the two-map odd-xor witness shows that every one of
the `2^K` control profiles must be distinguished; at `N=2^n`, the required
profile has `K=2^(Omega(n))` bits and violates Theorem 8.3's polynomial sampler
complexity.
