---
rg: 2
id: f2-leavitt-path-hosts-via-khanh-transfer
kind: route
title: Run the Khanh transfer over a graph algebra with graph division, determinant K-theory, cancellation and a trivial centre
target: f2-leavitt-path-unit-groups-fp-simple-steinberg
requires:
  - leavitt-path-k-theory-over-finite-fields-via-det
  - leavitt-path-algebras-have-simultaneous-strong-division
  - purely-infinite-leavitt-path-v-monoid-cancellation
  - simple-leavitt-path-algebra-center-is-coefficient-field
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

Follows Sections 2--4 of the reviewed B⊗L artifact, with four substitutions.

1. **Leavitt family and leaf coordinates.** Cancellation and `[1] = 0` give
   `L ≅ L^2`, hence isometries `e, f` with `ee* + ff* = 1` and `L ≅ M_m(L)` for
   every `m`.
2. **Division.** `leavitt-path-algebras-have-simultaneous-strong-division` replaces
   Lemma 2.2's multiplier. `ker u_i` has class `0` and is nonzero, so it is `≅ L`
   by cancellation. This is Proposition 2.4 (frame extension) and Corollary 2.5.
3. **Stable input.** `leavitt-path-k-theory-over-finite-fields-via-det` gives
   `K_1 = K_2 = 0` when `D != 0`, and all `K_n = 0` for `n >= 1` when `D = ±2^k`.
   These feed Proposition 3.1 and Khanh's Theorem 2.2 in the degrees used. With
   Lemma 5.3 (Menal--Moncasi GE for simple rings with strong division, and
   `K_1 = 0`), Theorem 5.1 gives `St_r ≅ GL_r` for `r >= 3`, and Krstić--McCool
   gives finite presentation.
4. **Simplicity.** The Lean theorems `rootDetection_of_leavittFamily` and
   `isSimpleGroup_of_rootDetection` are applied on paper:
   - Leavitt family: from 1;
   - `hdiv`: case `s = 1` of 2;
   - `hcentral`: `simple-leavitt-path-algebra-center-is-coefficient-field`;
   - nontriviality: `x_12(1) != 1`.

The target stays open until both citation claims are established and the
transfer is reviewed.
