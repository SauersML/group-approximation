---
rg: 2
id: kazhdan-trace-amenable-iff-qd-iff-fd-limit-proof
kind: route
title: "Finite-dimensional limits are QD, QD traces are amenable, and Ozawa's Theorem 7.4 closes the circle"
target: kazhdan-trace-amenable-iff-qd-iff-fd-limit
requires:
  - ozawa-kazhdan-liftable-traces-are-fd-limits
---

- **(c) ⟹ (b).** *-homomorphisms are ucp and exactly multiplicative.
- **(b) ⟹ (a).** |tr(x)| ≤ ‖x‖, so operator-norm asymptotic multiplicativity gives
  tr(φ_n(ab*) − φ_n(a)φ_n(b)*) → 0, which is Ozawa Thm 6.1(ii).
- **(a) ⟹ (c).** Thm 6.1 (ii) ⟹ (ii') says τ is liftable, and Thm 7.4 gives the π_n.
- **Canonical trace, RF ⟹ (c).** Enumerate Γ∖{e} = {g_1, g_2, …}. Choose finite-index normal K_i ∌ g_i and
  put N_m = K_1∩…∩K_m. Then π_m = λ_{Γ/N_m}∘(quotient) is a *-homomorphism into M_{[Γ:N_m]}, and
  tr π_m(u_g) = [g ∈ N_m] → δ_{g,e}. By linearity, density of C[Γ] and contractivity, tr∘π_m → τ_Γ weak*.
- **Canonical trace, (a) ⟹ RF.** τ_Γ amenable means (F) (Def. 7.2 with Thm 6.1), and the last sentence of
  Thm 7.4 gives residual finiteness.

The full proof is in `research/artifacts/un-traces-2026-09-13-part1.md` §2.
