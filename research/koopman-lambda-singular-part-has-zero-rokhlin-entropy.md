---
rg: 2
id: koopman-lambda-singular-part-has-zero-rokhlin-entropy
kind: claim
title: Rokhlin entropy vanishes on every Koopman subspace singular with the regular representation
distinct_from:
  bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups: that asks for maximal Bernoulli Rokhlin entropy on simple Kazhdan hosts; this is Seward's representation-theoretic vanishing theorem over every countably infinite group, which constrains where positive entropy can live and never supplies any.
artifacts:
  - research/artifacts/rokhlin-lower-bound-mechanisms-2026-09-12.md
---

**ESTABLISHED (literature import).** B. Seward, *The Koopman representation and
positive Rokhlin entropy*, arXiv:1804.05270v1, read from the PDF text extracted
on MSI on 2026-09-12. Section 1 of the artifact has the verbatim quotes.

**Theorem 1.2.** Let `G ↷ (X, μ)` be a free p.m.p. action with Koopman
representation `ρ`, and let `λ` be the left-regular representation. If `H` is a
closed `ρ(G)`-invariant subspace of `L²(X, μ)` and `ρ|_H` is singular with `λ`,
then `h_G(σ-alg(H)) = 0`.

**Corollary 1.3.** If an orthogonal representation `π` of a countably infinite
group is singular with the real left-regular representation, then the Gaussian
action induced by `π` has Rokhlin entropy `0`.

Seward also notes that `λ^⊕N` embeds into the Koopman representation of every
free ergodic p.m.p. action with positive Rokhlin entropy.

**Use in this graph.**
- Any free ergodic action witnessing
  `leavitt-unit-group-has-positive-rokhlin-entropy-action` or
  `tester-host-has-positive-rokhlin-entropy-action` carries its entropy on the
  part of its Koopman representation that is not singular with `λ`. So Gaussian
  actions of representations singular with `λ` cannot be witnesses.
- This is a necessary condition, not a lower bound. The uniform Bernoulli shift
  over any countably infinite group has Koopman representation `λ^⊕N` on the
  orthocomplement of the constants, so it passes the test whatever its
  entropy.

Route: [[koopman-lambda-singular-zero-entropy-citation]].
