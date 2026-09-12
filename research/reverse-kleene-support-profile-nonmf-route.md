---
rg: 2
id: reverse-kleene-support-profile-nonmf-route
kind: route
title: Feed the seeded switch into reverse Kleene and identify the nonhalting free-product branch
target: reverse-kleene-support-profile-nonmf
requires:
  - authenticated-opnorm-challenge-compiler
  - threshold-free-reverse-kleene-mf-higman
  - literal-central-mark-corona-invisible
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
---

Use the compiler supplied by `authenticated-opnorm-challenge-compiler`.
The fixed-point program enumerates proofs that its own marked word is trivial.
The HALT semantics rule out halting, so the NONHALT semantics put that same
nontrivial word in the MF radical.

For the seeded switch, more is known than the abstract theorem needs: the
nonhalting presentation is literally `E*Z`.  It is already finitely
presented, the free-factor embedding keeps the marked word nontrivial, and
MF-radical functoriality keeps it invisible.  Thus effective Higman is
available but unnecessary for this instance.
