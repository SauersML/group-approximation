---
rg: 2
id: hyperbolic-groups-satisfy-boone-higman
kind: claim
title: Every hyperbolic group embeds in a finitely presented simple group
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that imports Zaremsky's theorem for finitely presented self-similar inputs, which are residually finite; this imports the Belk--Bleak--Matucci--Zaremsky theorem for hyperbolic inputs, proved through contracting rational similarity groups, with no residual finiteness assumed.
artifacts:
  - research/artifacts/boone-higman-frontier-2026-09-12.md
---

**ESTABLISHED (literature import).** Every hyperbolic group embeds in a
finitely presented simple group, and so satisfies `boone-higman-conjecture`.

Source: J. Belk, C. Bleak, F. Matucci, M. C. B. Zaremsky, *Hyperbolic groups
satisfy the Boone-Higman conjecture*, arXiv:2309.06224 (v3, 20 August 2025;
Duke Math. J.). By the abstract, the proof embeds each hyperbolic group in a
contracting rational similarity group, and those in turn embed in finitely
presented simple groups. The same paper also covers contracting self-similar
groups.

The survey arXiv:2306.16356v3, Theorem 5.1, lists "(13) Hyperbolic groups."
among the groups that "embed into finitely presented simple groups".

## Scope

Subgroups inherit the conclusion, so every group that embeds in a hyperbolic
group satisfies Boone--Higman. Nothing here is reproved, and there is no Lean
counterpart.
