# bh-ref-e1-b (referee, SFT-lift half of the gate E1 route)

Landed b5c7787d69: Referee sections on four nodes.
- keyed-diversification-slots-give-plane-constant-minimal-lifts
- free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2
- keyed-slots-bypass-the-phase-field-on-boundary-geometry
- minimal-free-sft-overgroups-via-storage-column-free-subshifts

Source read: Durand–Romashchenko arXiv:1802.01461 (TeX v4, on MSI at
/projects/standard/hsiehph/sauer354/bh-ref-e1-b/src/arxiv-4.tex), §3.2 (p1)–(p4), Cases 1–3, the
slot frame, §4.1 letter delegation, and minimal-simulation Claims 1–5.

Verdicts:
- **Keyed-slot lift: PASS (design level), conditional on G1.** Slot keys must be the full level-K
  input field (τ_K, τ_K^(s), τ_{K+1}), not τ_K alone. Windows at the computation input row or on
  input wires depend on the other fields. Repair: children carry κ_K, slots are keyed and display
  real κ_K, and (G) adjusts. G2 is cosmetic: i should be partial.
- **Bypass node:** Parts 1–3 PASS. Part 4 is correctly OPEN, and bh-g3-topfree supplies its repair
  (ii).
- **Route composition: PASS.** The step 3→4 convention inversion is not stated (cosmetic).
  bh-ref-e1-a passed steps 1–3 independently. So E1 (P1) holds modulo G1 being written in.
