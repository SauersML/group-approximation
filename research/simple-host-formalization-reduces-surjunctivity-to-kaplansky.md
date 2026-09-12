---
rg: 2
id: simple-host-formalization-reduces-surjunctivity-to-kaplansky
kind: route
title: Formalize a left inverse over the simple host, then linearize at a constant configuration
target: stably-finite-simple-hosts-are-binary-power-surjunctive
requires:
  - binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

1. Let `S` be finitely generated simple with `F_2[S]` stably finite, and let `tau` on `(F_2^n)^S` be
   injective with left inverse `sigma`.
2. By the first prerequisite, representatives satisfy `sigma~ o tau~ = id` formally.
3. `M_n(F_2[S])` is directly finite. By the second prerequisite, `tau o sigma = id`, so `tau` is
   surjective.
