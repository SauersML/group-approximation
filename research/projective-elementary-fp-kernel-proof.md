---
rg: 2
id: projective-elementary-fp-kernel-proof
kind: route
title: Combine upward central-extension finiteness with the Steinberg presentation and quotient-kernel criterion
target: projective-elementary-fp-kernel-criterion
requires: [fg-central-extension-of-fp-group-is-fp, steinberg-finite-presentation-and-kazhdan-theorem, fp-quotient-iff-kernel-finitely-normally-generated]
artifacts:
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
---

The Steinberg theorem supplies finite presentation, and therefore finite
generation, of St_n(R). Its quotient E is finitely generated.

Apply fg-central-extension-of-fp-group-is-fp to E and its actual center
Z(E). This proves (1) iff (2), including the implication from projective
finite presentation back to finite presentation of E.

Apply fp-quotient-iff-kernel-finitely-normally-generated to St_n(R)->E.
It says E is finitely presented iff K is finitely normally generated in
St_n(R). Keeping the center clause unchanged proves (2) iff (3).

The central-extension lemma is applied to E->P, never to St_n(R)->E.
This distinction is essential over arbitrary noncommutative R.

