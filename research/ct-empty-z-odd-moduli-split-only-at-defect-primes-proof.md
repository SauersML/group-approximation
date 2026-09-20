---
rg: 2
id: ct-empty-z-odd-moduli-split-only-at-defect-primes-proof
kind: route
title: "A digit-sum-preserving base-4 north-south element for the obstruction; for localization, Theorem 2's trivial blocks composed along an attractor-repeller flow edge, evaluated at the attractor"
target: ct-empty-z-odd-moduli-split-only-at-defect-primes
requires:
  - ct-empty-z-cone-partition-question-is-decidable
  - ct-z-residue-partition-certificates-live-on-s-adic-coordinates
  - ct-p-z-is-a-one-vertex-k-graph-full-group
---

Lane proof (bh-free-58, 2026-09-19), not reviewed. The argument is in the body of
`ct-empty-z-odd-moduli-split-only-at-defect-primes`. It uses:
- item 3 of the k-graph node, for membership;
- Lemma A (flow components) of the cone node;
- the "blocks trivial mod ℓ" conclusion of Theorem 2 of the S-adic node, whose proof needs only
  that a power of `ĝ` fixes every part.
