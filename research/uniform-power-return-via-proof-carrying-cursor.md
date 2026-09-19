---
rg: 2
id: uniform-power-return-via-proof-carrying-cursor
kind: route
title: Address a repeated-squaring execution but authenticate only its constant-size return port
target: uniform-power-return-self-hash
requires: [conjugacy-addressed-opnorm-challenges-are-lossless, proof-carrying-power-return-terminal-authentication]
---

Use a commutator-type cursor and represent the exponent as data in a
repeated-squaring execution.  Do not replay the execution to verify it.  The
machine should emit a proof-carrying terminal object whose return discrepancy
is a literal conjugate of one of finitely many root checks.  This would make
the operator-norm verification cost independent of the exponent and runtime.

The missing theorem is the finite syntax and exact completeness of that
proof-carrying return interface.  Self-reference is not used until this
analytic compiler exists.
