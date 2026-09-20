---
rg: 2
id: thompson-f-trace-spread-caps-the-census-ratio-proof
kind: route
title: A tracial ultraproduct of relator-almost-solutions is a character of F, and the character simplex forces equal traces on F' minus the identity
target: thompson-f-trace-spread-caps-the-census-ratio
requires:
  - thompson-f-character-simplex
artifacts:
  - research/artifacts/thompson-f-census-trace-spread-2026-09-17.md
---

Full proof: artifact, Section 1.

**Item 1.**
1. Suppose item 1 fails for `(S, eta)`. Then there are pairs `(U_k, W_k)` in `U(n_k)` with `sigma_S >= eta` and
   `max_i e(R_i) <= 1/k`.
2. Along a nonprincipal ultrafilter, the tracial ultraproduct `prod^omega (M_{n_k}, tr)` contains unitaries
   `u = [U_k]` and `v = [W_k]` with `R_i(u, v) = 1`, because `||R_i(u,v) - 1||_2 = lim_omega ||R_i(U_k, W_k) - I||_2 = 0`.
3. So `a -> u, b -> v` is a homomorphism `pi` of `F`. `phi = tau o pi` is a character of `F`, with
   `phi(w) = lim_omega tr w(U_k, W_k)` for each word `w`.
4. By `thompson-f-character-simplex`, `phi = t tau_reg + (1-t) chi_ab`. So `phi(w) = 1 - t` in `[0, 1]` for every `w` in `F' \ {e}`.
   The limit trace vector therefore lies on the constant segment.
5. `sigma_S` is continuous in the trace vector, so the limit vector would have to be at distance at least `eta`
   from that segment. This is a contradiction.
6. Since `e(c) <= 4`, the ratio bound follows.

**Item 2.** Take `S = {c}`. From `e(c) = 2 - 2 Re tr c`, the condition `e(c) >= tau` gives `Re tr c <= 1 - tau/2 < 0`, so
`sigma_{c} >= tau/2 - 1`. Item 1 then applies.

**Item 3.** This is the contrapositive of item 1, taken along any subsequence.
