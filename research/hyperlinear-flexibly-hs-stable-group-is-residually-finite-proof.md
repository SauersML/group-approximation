---
rg: 2
id: hyperlinear-flexibly-hs-stable-group-is-residually-finite-proof
kind: route
title: Stabilize a separating approximation, read off maximal almost periodicity, apply Malcev
target: hyperlinear-flexibly-hs-stable-group-is-residually-finite
requires: []
---

## Direct proof

1. **A separating approximation.** Since `Γ` is hyperlinear, there are asymptotic
   representations `π_n: Γ -> U(d_n)` with `||π_n(g) - I||_2 -> √2` for every
   `g != e`.
2. **Stabilize.** Flexible stability gives `ρ_n: Γ -> U(D_n)`, `D_n >= d_n`, with
   `||π_n(g) - P_n ρ_n(g) P_n||_2 -> 0`. For `g != e`, the triangle inequality gives
   `||P_n(ρ_n(g) - I)P_n||_2 >= ||π_n(g) - I||_2 - o(1) -> √2`. So `ρ_n(g) != I` for
   large `n`.
3. **Maximal almost periodicity.** Every `g != e` is moved by some genuine
   finite-dimensional unitary representation of `Γ`.
4. **Malcev.** `ρ(Γ)` is a finitely generated linear group, hence residually
   finite. A finite quotient of `ρ(Γ)` separating `ρ(g)` from `I` is a finite
   quotient of `Γ` not killing `g`.

∎
