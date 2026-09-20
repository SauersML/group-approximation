---
rg: 2
id: amenable-kernel-extra-kernel-is-tracial-gns-radical-proof
kind: route
title: "Prove the extra kernel of an amenable-kernel relation quotient is exactly its tracial GNS radical"
target: amenable-kernel-extra-kernel-is-tracial-gns-radical
requires:
  - amenable-kernel-quotient-traces-factor-reduced
artifacts:
  - research/artifacts/Cairn_Baum_Connes_General_Attempt.md
---

Factorization puts E in every tracial GNS kernel. The faithful
canonical trace of C_r^*(Q), pulled back along q̄, has GNS kernel
exactly E, giving equality. For any *-homomorphism φ into a faithfully
traced algebra, normalize the pulled-back bounded positive trace if
nonzero; if it is zero, faithfulness forces φ=0. Apply faithfulness
to φ(e)^*φ(e) for e∈E. This includes finite-dimensional targets.

This is a written deduction integrated from the supplied attempt, not
an independent referee report or a Lean proof.
