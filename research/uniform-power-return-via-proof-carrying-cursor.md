---
rg: 2
id: uniform-power-return-via-proof-carrying-cursor
kind: route
title: Address a repeated-squaring execution but authenticate only its constant-size return port
target: uniform-power-return-self-hash
requires: [conjugacy-addressed-opnorm-challenges-are-lossless, proof-carrying-power-return-terminal-authentication]
artifacts:
  - research/artifacts/power-return-certificates-have-linear-area-2026-09-08.md
---

Use a commutator-type cursor and represent the exponent as data in a
repeated-squaring execution.  Do not replay the execution to verify it.  The
machine should emit a terminal word `c_m` whose discrepancy from the
addressed conjugate of `w` is a literal conjugate of one fixed root
check. Separately use the prerequisite's uniform semantic estimate
`||c_m(U)-w(U)^m|| <= C_sem Def_R(U)`. The triangle inequality
then gives the complete return bound with constant `1+C_sem`.

The missing theorem includes that semantic norm estimate, not just
the existence of the terminal word or its equality in the presented
group. The linear-area theorem excludes paying for both parts with
uniformly bounded relator certificates, even for a commutator cursor.
No such analytic compiler has been constructed.
