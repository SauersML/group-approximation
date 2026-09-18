---
rg: 2
id: houghton-far-commutation-six-rays-by-halving-pours
kind: route
title: Halve pours using two auxiliary rays, then reroute the two transpositions onto disjoint rays
target: houghton-far-commutation-has-quadratic-log-area-for-six-rays
requires: []
artifacts:
  - research/artifacts/zp-houghton-pours-2026-09-17.md
---

Complete proof in `research/artifacts/zp-houghton-pours-2026-09-17.md`, §§0–3.

1. Work in a finite presentation `P` that adds the letters `λ_xy` and `τ_x`, and
   all trivial words of length `<= 40` in them, to Lee's presentation. Areas in
   Lee's presentation are at most a constant times areas in `P`.
2. The pour `E^c_(a,b)(m) = λ_ac^m λ_cb^m` is supported on rays `a,b`, for every
   `c`. Let `W(m)` be the cost of changing `c`. Splitting `m = m_1 + m_2` and using
   two rays `e,f` outside `{a,b,c,d}` (so `n >= 6`) gives
   `W(m_1+m_2) <= 2W(m_1) + 2W(m_2) + 4m_1m_2 + 2m_1`. The inner pours are moved
   to the disjoint ray sets `{c,d,e}` and `{a,b,f}` and commuted letterwise. So
   `W(m) ≼ m^2 log m`.
3. Rerouting `λ_xu^i X λ_ux^i` to `λ_xu'^i X λ_u'x^i` costs
   `2W(i) + 2i|X| + 4i`.
4. For `w_k = [τ_a, D^b_a(k)]`:
   - conjugate by `λ_ab^(⌈k/2⌉)`;
   - move `τ_a` to ray `b` with a length-6 relator;
   - reroute the two transpositions onto the ray sets `{b,c}` and `{a,d}`;
   - commute letterwise.

   The total cost is `O(k^2 log k)`.
