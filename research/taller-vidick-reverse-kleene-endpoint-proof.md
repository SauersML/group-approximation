---
rg: 2
id: taller-vidick-reverse-kleene-endpoint-proof
kind: route
title: Split the self-referential proof search into its two branches and expose the missing proof-gap crossing
target: reverse-kleene-does-not-remove-tv-completeness-loss
requires:
  - taller-vidick-lcs-re-hardness
  - taller-vidick-positive-noise-fixed-support-reweighting
artifacts:
  - research/artifacts/taller-vidick-reverse-kleene-endpoint-audit-2026-08-21.md
---

For its own index, let the machine enumerate normal-closure certificates for
`J=1` in the output solution group and halt on the first certificate `D`.
Nonhalting makes `J` algebraically nontrivial, and the cited Taller--Vidick
NONHALT bound supplies the desired quantum gap.  If it halts, the source is a
HALT instance and only has value at least `1-epsilon`.  Telescoping the finite
certificate `D` through the standard near-perfect-LCS approximate
representation gives a computable positive upper gap `gamma(D)`.  These two
bounds conflict only when `epsilon<gamma(D)`, a comparison unavailable when
the output was formed.

At positive noise every mask has positive probability; at zero noise all but
the constant-one mask disappear.  The Fourier decoder bound itself is
proportional to `epsilon`, and the repetition parameter changes with
`epsilon`.  Hence neither taking a limit nor dovetailing output instances
transfers the certificate with a controlled gap.  Waiting for a crossing
certificate invalidates the inference from nonhalting to `J!=1`.
