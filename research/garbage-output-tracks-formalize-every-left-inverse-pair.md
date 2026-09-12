---
rg: 2
id: garbage-output-tracks-formalize-every-left-inverse-pair
kind: claim
title: Every left-inverse pair becomes formalizable once a functionally zero output track is added, and this certifies nothing
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that refutes formalizability on the original alphabet; this shows the refutation disappears with one extra output-only track that is zero on points, which carries no linearization content because the Jacobians are rectangular.
  injective-binary-automata-are-stably-formalizable: that asks for square stabilization, with identity tracks read as inputs; this is the rectangular calibration, where the extra tracks are outputs only, and it holds for every pair.
artifacts:
  - research/artifacts/stable-formalization-erasure-audit-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `p` be prime, `G` any group, and `(τ, σ)` a left-inverse pair on `(F_p^n)^G` with representatives
`τ~`, `σ~`. Put `d(X) = X − σ~(τ~(X))`.

**Claim.**
- The polynomial map `X ↦ (τ~(X), d(X))` represents the automaton `x ↦ (τ(x), 0)` from `(F_p^n)^G`
  into `(F_p^(2n))^G`.
- It has the formal left inverse `(U, E) ↦ σ~(U) + E`.

**Why it certifies nothing.**
- At a constant configuration the Jacobians of this pair form a rectangular one-sided inverse pair
  over `F_p[G]`, and such pairs exist over every ring.
- So the linearization argument of `formal-polynomial-strict-pairs-need-unstable-linearization` gets
  no grip.
- The content of a stable formalization is exactly that its extra tracks are square: inputs as well
  as outputs.

Proof: Section 1 of the artifact.
