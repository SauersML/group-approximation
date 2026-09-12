---
rg: 2
id: simple-host-formalizability-specializes-to-the-v-marker
kind: route
title: Thompson's V is a finitely generated simple host, and the marker involution is a binary left-inverse pair on it
target: thompson-v-marker-involution-is-formalizable
requires:
  - binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

1. **`V` is a finitely generated simple group.** This is classical (Higman; Thompson), imported at
   statement level.
2. **The pair.** `tau_g` is an involution on `{0,1}^V`, so `(tau_g, tau_g)` is a binary left-inverse pair.
3. **Specialize.** The prerequisite gives representatives with `tau~ o tau~ = id` formally.

A refutation of the target therefore refutes the prerequisite.
