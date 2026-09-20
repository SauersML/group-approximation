---
rg: 2
id: amenable-kernel-quotient-traces-factor-reduced-proof
kind: route
title: "Prove every trace on an amenable-kernel relation quotient factors through the reduced quotient group"
target: amenable-kernel-quotient-traces-factor-reduced
requires:
  - bkko-reduced-traces-concentrate-on-amenable-radical
artifacts:
  - research/artifacts/Cairn_Baum_Connes_General_Attempt.md
---

Theorem 3.1 of the artifact proves R_Γ=π⁻¹(R_Q) by amenability of
extensions. The required trace-support theorem reduces τ to R_Γ.
Amenability identifies its full and reduced group algebras, so the
restriction descends through R_Γ/N=R_Q. That state is Q-conjugation
invariant. Composing it with E_(R_Q) gives a trace on C_r^*(Q);
compare group-ring values and use surjectivity for uniqueness.

This is a written deduction integrated from the supplied attempt, not
an independent referee report or a Lean proof.
