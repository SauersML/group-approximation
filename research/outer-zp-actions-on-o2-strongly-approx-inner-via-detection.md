---
rg: 2
id: outer-zp-actions-on-o2-strongly-approx-inner-via-detection
kind: route
title: Detection makes the generator KK^G-trivial, and Gabe--Szabó uniqueness plus averaging makes it strongly approximately inner
target: outer-zp-actions-on-o2-are-strongly-approximately-inner
requires:
  - zp-restriction-and-crossed-product-detect-kk-g-contractibility
  - zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner
---

Assume detection at `p`, and let `α` be an outer `Z/p`-action on `O_2`.

1. `Res(O_2, α) = O_2 ≃_KK 0`.
2. By item 4 of `zp-restriction-trivial-splits-cellular-plus-phantom`, which
   `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner` consumes,
   `[α_ω] = 1` in `KK^G`.
3. Item 1 of `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner` turns
   this into a continuous path of fixed-point unitaries `w_t` with
   `Ad(w_t) → α_ω`.
4. Sampling `t = n` gives the claim.
