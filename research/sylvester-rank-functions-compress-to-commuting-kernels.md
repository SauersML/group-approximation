---
rg: 2
id: sylvester-rank-functions-compress-to-commuting-kernels
kind: claim
title: A Sylvester rank function compresses to the kernel of an element commuting with a subring, and commuting pairs satisfy the triangular count
distinct_from:
  sylvester-rank-functions-descend-to-quotients-and-compressions: that compresses to quotients by two-sided ideals and to images of commuting elements; this compresses to kernels of commuting elements, which are right annihilators and neither of those.
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w7-sylv-global`, route `sylvester-rank-functions-compress-to-commuting-kernels-proof`;
artifact Section 3; verified PASS by `w4-vf-linear-b`, Section 39.3 of
`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, ae0a4005ef).

Let `rho` be a Sylvester matrix rank function on a unital ring `S`, `C` a unital subring, and `P` in `S` with
`c P = P c` for every `c` in `C`. Write `P_n = P I_n`.

1. **Kernel compression.** If `rho(P) < 1`, then
   `sigma(A) := (rho([P_n; A]) - n rho(P)) / (1 - rho(P))`, for matrices `A` over `C` with `n` columns,
   is a Sylvester matrix rank function on `C`.
2. **Triangular count.** If `T` in `S` commutes with `P`, then `rho([P; T]) + rho(P T) <= rho(P) + rho(T)`.

**Regular comparison.** In a faithful regular rank ring, `sigma` is the normalized rank of `A` on the right
annihilator of `P`. That is the kernel corner of Proposition 4.1 of
`research/artifacts/two-root-defect-descent-gap-2026-09-12.md`, and part 2 is `ker P + ker T <= ker PT`. Here no
idempotent and no annihilator is used.

## Attempts

Established on paper, not open. Proof in artifact Section 3 (Lemmas 3.1 and 3.2).
