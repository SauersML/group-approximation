---
rg: 2
id: borel-structurability-invariants-are-bernoulli-base-blind-proof
kind: route
title: Map every free shift part into the 2-shift class-bijectively and include the 2-shift back
target: borel-structurability-invariants-are-bernoulli-base-blind
requires:
  - seward-tucker-drob-free-borel-actions-map-to-2-shift
artifacts:
  - research/artifacts/gk-p-inf-wild-borel-and-topological-2026-09-12.md
---

Proposition 1.1 of the artifact.

1. The prerequisite gives a class-bijective Borel map `Free(q^G) -> Free(2^G)`, so
   `J(Free(q^G)) <= J(Free(2^G))`.
2. The symbol inclusion `{0,1} ⊂ {0,...,q-1}` induces an equivariant Borel injection
   `2^G -> q^G`. It preserves stabilizers, so it maps free points to free points.
3. An equivariant map between free actions is bijective from each orbit onto an orbit, so the
   inclusion is class-bijective and `J(Free(2^G)) <= J(Free(q^G))`.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 9 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
