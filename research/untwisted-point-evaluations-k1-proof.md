---
rg: 2
id: untwisted-point-evaluations-k1-proof
kind: route
title: Contract the constant summands, then pull back a stable-range null-homotopy
target: untwisted-point-evaluations-kill-k1-obstructions
requires: [bundle-endomorphism-unitaries-stable-range]
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

1. `U(r)` is path connected; choose paths `w_l` from `u(x_l)` to `1`. The path
   `pi^*u ⊕ diag(w_1(t), ..., w_m(t))` joins `psi(u)` to
   `pi^*u ⊕ 1_(m r) = pi^*(u ⊕ 1_(m r))`.
2. Here `u ⊕ 1_(m r)` is a unitary of `Gamma(X, End(E ⊕ theta^(m r)))`. Its
   `K_1` class is the image of `[u] = 0` under the corner inclusion, hence
   zero.
3. The bundle `E ⊕ theta^(m r)` has rank `r(m+1)` and `d + 1 <= 2 r (m+1)`.
   By the prerequisite (`k = 0`) its unitary component group injects into
   `K_1`, so `u ⊕ 1_(m r)` is null-homotopic over `X`.
4. Pullback of sections along `pi` is a unital *-homomorphism, so it carries
   that null-homotopy to one of `pi^*(u ⊕ 1_(m r))`, and `psi(u)` is
   null-homotopic.

For the consequence in the target: with `m_j >= 1` and `d_j <= 4 r_j - 1` the
inequality holds at every stage. Every K1-null unitary of `A_j` therefore
dies in `A_(j+1)`, and by finite-stage detection of the K1 class the limit is
K1-injective. The full write-up is Proposition E and Corollary E1 of the
linked constraint-map artifact. Square.
