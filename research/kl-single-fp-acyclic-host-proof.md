---
rg: 2
id: kl-single-fp-acyclic-host-proof
kind: route
title: A finitely presented counterexample embeds in the universal finitely presented acyclic group
target: kl-holds-iff-it-holds-over-one-fp-acyclic-group
requires: [kl-counterexample-can-be-finitely-presented, universal-fp-acyclic-group-exists]
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

Artifact §4(b).
- **If the conjecture fails, it fails over `U_ac`.** Take a failure
  `(P, w, a)` with `P` finitely presented (first prerequisite). `P` is
  recursively presented, so it embeds in `U_ac` (second prerequisite). The
  collapse identity in `P * <t>` persists in `U_ac * <t>`, and `a != 1` in
  `U_ac`.
- **The converse is trivial.** A failure over `U_ac` is a failure. ∎
