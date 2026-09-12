---
rg: 2
id: mf-to-weak-qd-citation-has-unproved-lifting-step
kind: claim
title: The MF-to-weak-quasidiagonality citation omits a completely positive approximation step
invalidates:
  - mf-kazhdan-without-finite-quotients-citation
  - simple-kazhdan-full-mf-radical-proof
  - exact-kazhdan-radical-kernel-cannot-be-lef-proof
artifacts:
  - research/artifacts/operator-mf-weak-quasidiagonality-audit-2026-09-11.md
distinct_from:
  mf-kazhdan-group-without-finite-quotients-is-trivial: this audits the cited proof's missing lifting step; it neither asserts nor refutes that group-theoretic conclusion
---

The derivation in `mf-kazhdan-without-finite-quotients-citation` is incomplete.
Its application of Dadarlat's Proposition 3.19 needs weak quasidiagonality,
which includes unital completely positive approximations of `C*(G)`.
Operator-MF supplies approximate unitary homomorphisms instead. Definitions
give weak quasidiagonality implies operator-MF, by polar decomposition.
They do not supply the converse construction required by the cited route.

The printed introductory arrow in arXiv:2007.12655v2 is acknowledged in the
artifact and conflicts with other statements in that source. An explicit
separating MF approximation to `C_2` in the artifact has no positive
extensions, proving that a supplied MF witness cannot simply be extended
as asserted by a definitional reading of that arrow. This does not refute
the existence of another completely positive approximation, nor the
underlying Kazhdan MF claim. It invalidates the listed proof routes, which
each require this same unproved operation, rather than refuting their target
claims. The LEF route reaches MF first and then uses the same missing step.
