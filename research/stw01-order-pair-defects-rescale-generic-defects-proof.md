---
rg: 2
id: stw01-order-pair-defects-rescale-generic-defects-proof
kind: route
title: Rescale a positive pair affinely and split off the scalar parts on commutative subalgebras
target: stw01-order-pair-defects-rescale-generic-defects
requires: []
---

Full proof: Section 1 of `research/artifacts/stw01-order-pair-rescaling-2026-09-12.md`.

1. **Spectrum of `h`.** `sp(x) ⊂ [0, 1]`, so `sp(h) ⊂ [1/2, 1/2 + eps] ⊂ [0, 1]` because
   `eps <= 1/5`.
2. **The room.** Expanding, `h - h^2 = (1/2 + eps x) - (1/2 + eps x)^2 = (1/4) 1 - eps^2 x^2`.
   Since `0 <= x^2 <= 1`, this gives `(1/4 - eps^2) 1 <= h - h^2 <= (1/4) 1`.
3. **(OP).** `k >= s 1 >= 0`, since `y >= 0` and `s >= 0` (because `eps + eps^2 <= 6/25 < 1/4`).
   Also `k <= (s + eps) 1 <= (1/4 - eps^2) 1 <= h - h^2`. The universal property of `U`
   gives `psi`.
4. **Squeeze.** `h - h^2 <= (1/4) 1` gives `4s (h - h^2) <= s 1 <= k`, and `4s = 1 - 4 eps - 4 eps^2`
   for the extreme `s`.
5. **The defect.** A quasitrace is linear on every commutative C*-subalgebra. The three
   pairs `((1/2 + s) 1, eps (x + y))`, `((1/2) 1, eps x)` and `(s 1, eps y)` lie in
   `C*(1, x + y)`, `C*(1, x)` and `C*(1, y)` respectively. So

   ```text
   sigma(h + k) = (1/2 + s) sigma(1) + eps sigma(x + y),
   sigma(h)     = (1/2) sigma(1) + eps sigma(x),
   sigma(k)     = s sigma(1) + eps sigma(y),
   ```

   and subtracting gives `D(h, k) = eps D(x, y)`.

**Trust boundary.** Only the axioms of a bounded 2-quasitrace (linearity on commutative
C*-subalgebras) and the universal property of `U`. No monotonicity, continuity, Douglas
factorization or group algebra is used.
