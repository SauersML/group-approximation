---
rg: 2
id: sl3-gao-qwep-test-case-proof
kind: route
title: Apply residual finiteness and Gao's scalar QWEP-inclusion question
target: sl3-scalar-terminal-is-gao-qwep-inclusion-test-case
requires: []
artifacts:
  - research/artifacts/sl3-re-hecke-bimodule-audit-2026-08-21.md
---

Both arithmetic groups are finitely generated linear groups over a
characteristic-zero field, hence residually finite.  Their group factors
are therefore Connes embeddable and QWEP.  Gao's Problem 6.1 asks whether
an inclusion `P subset Q` must be `RE/C_scalar` whenever the ambient finite
von Neumann algebra `Q` is QWEP (equivalently, whether the relevant
amalgamated free product over a QWEP subalgebra remains QWEP).

Apply that question to `P=N`, `Q=M`.  A universal positive answer gives
scalar RE for this inclusion.  Conversely, failure of scalar RE here is an
explicit counterexample with both factors QWEP.  These are exactly the two
implications asserted in the claim.

