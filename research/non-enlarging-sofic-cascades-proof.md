---
rg: 2
id: non-enlarging-sofic-cascades-proof
kind: route
title: Induction along the cascade with routing preservation, descent and equal-alphabet rigidity
target: non-enlarging-sofic-window-cascades-cannot-compress
requires:
  - injective-same-alphabet-sofic-codes-preserve-uniform-measure
  - measurable-certificate-routing-preserves-bernoulli-measure
  - bernoulli-codes-descend-to-window-subgroup
  - single-maximal-stage-routed-codes-cannot-compress
artifacts:
  - research/artifacts/non-expanding-sofic-cascades-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Section 3 of `research/artifacts/non-expanding-sofic-cascades-2026-09-12.md`.

1. **Each stage is injective for its input.** Lusin–Souslin makes every partial image Borel and of full measure,
   and each stage is injective on it.
2. **One stage with uniform input.**
   - Routing preserves the measure (Theorem A), and (P)-stages preserve it by definition.
   - A (W)-stage descends to its window, so it cannot shrink the alphabet (rigidity, Part 1).
   - When it keeps the alphabet, rigidity Part 2 with coset lifting makes its output uniform.
3. **Induction** gives items 1–3.
4. **Item 4.** A uniform output of the first enlarging stage would have a Borel inverse compressing a full shift
   over the sofic window, contradicting Part 1.
5. **Item 5** is steps 3–4 of the single-stage theorem.

Proposition H in Section 4 is an explicit cascade and needs no inputs.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including the equivariant
extension of the inverse in item 4, Proposition H and the continuous-decoder remark
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 10.2).
