---
rg: 2
id: module-quotient-k0-defects-are-trace-invisible-proof
kind: route
title: "Prove every bounded positive trace misses the liftable K-zero defect of a module quotient"
target: module-quotient-k0-defects-are-trace-invisible
requires:
  - amenable-kernel-quotient-traces-factor-reduced
  - module-evident-ideal-is-kernel-relation-ideal
  - module-k-defect-is-liftable-quotient-kernel
artifacts:
  - research/artifacts/Cairn_Baum_Connes_General_Attempt.md
---

The relation-ideal identification applies the amenable-kernel
factorization theorem with N=W. Naturality of the trace pairing
gives ρ_*(z)=σ_*(q̄_*(z))=0, and rescaling treats every bounded
positive trace. Localization identifies the prospective defect with
the liftable intersection. For torsion V the coefficient compact-open
projections form an approximate unit (e_i) for J. Vanishing of the
ideal K_0 image gives τ(e_i)=0. For a≥0 in J,
0≤e_i a e_i≤||a||e_i and e_i a e_i→a, so τ(J)=0. Descend to D,
then to B. Corollaries 3.3 and 4.3 give full proofs.

This is a written deduction integrated from the supplied attempt, not
an independent referee report or a Lean proof.
