---
rg: 2
id: weyl-algebra-over-q-is-lef-ring-not-matricial-over-q
kind: claim
title: The first Weyl algebra over Q is a simple LEF ring over the primes, embeds in no matrix ultraproduct over characteristic-zero fields, and has LEF elementary groups
artifacts:
  - research/artifacts/un-calibration-table-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed)** by `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q-proof`.

**Statement.** Let `A = A_1(Q) = Q⟨x, y⟩/(xy − yx − 1)`.
1. `A` is simple, and it is a domain.
2. No map `A → M_N(k)`, `k` a field of characteristic 0, is unital and exactly multiplicative on `{x, y}`. So `A` embeds in no
   algebraic ultraproduct `∏_ω M_(N_i)(k_i)` with every `k_i` of characteristic 0.
3. `A` embeds unitally in `∏_ω M_p(F_p)`, with `ω` on the primes, through `A_1(Z_(p)) → A_1(F_p) → End(F_p[x]/(x^p))`,
   `y ↦ −d/dx`. So `A` is a LEF ring: stably finite, with a faithful Sylvester matrix rank function.
4. For every `n >= 2`, `EL_n(A)` is LEF, MF and sofic. Neither `A` nor `EL_n(A)` is finitely generated, so `EL_n(A)` has no (T).

**UN calibration (U2, U3).** A simple, stably finite ring can fail to be matricial over its base field, and over every
characteristic-0 field, while its elementary groups are LEF. The ring condition that matches LEF of `EL_n` is the LEF ring, with
ultraproducts of matrix rings over varying finite fields, not "embeds in `∏_ω M_N(k)`". Row 13 of the calibration table.
