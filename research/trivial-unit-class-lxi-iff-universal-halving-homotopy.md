---
rg: 2
id: trivial-unit-class-lxi-iff-universal-halving-homotopy
kind: claim
title: K1-injectivity of properly infinite algebras with trivial unit class is equivalent to the halving homotopy in O_2 * C(T)
artifacts:
  - research/artifacts/lxi-halving-homotopy-and-extensions-2026-09-12.md
---

Let `U = O_2 *_C C(T)` be the full unital free product, with Cuntz generators `s_1, s_2` and free unitary
`z`. The following are equivalent.

1. `U` is K1-injective. Equivalently `O_2 *_C O_2` is, since `O_2 * O_2 ≅ O_2 * C(T)` by Blanchard's
   substitution `ι_2(s_k) ↦ z s_k`.
2. In every unital C\*-algebra `A` containing a Cuntz pair, every unitary `w` is homotopic to its halving
   `s_1 w s_1^* + s_2 s_2^*`. It suffices to check the universal case `z ~_h s_1 z s_1^* + s_2 s_2^*` in `U`.
3. Every unital properly infinite C\*-algebra `A` with `[1_A] = 0` in `K_0(A)` is K1-injective.

STW Problem LXI implies all three. The converse is open. It would need K1-trivial witnesses of an
arbitrary properly infinite `A` to survive in `A *_C O_2`. That is the same survival problem as the free
envelope of the LIX witness.
