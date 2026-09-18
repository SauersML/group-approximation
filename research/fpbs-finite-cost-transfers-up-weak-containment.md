---
rg: 2
id: fpbs-finite-cost-transfers-up-weak-containment
kind: claim
title: For every countable group, cost and relative cost over any subgroup are monotone under weak containment of free actions, so Bernoulli shifts have maximal cost
distinct_from:
  cost-is-constant-on-weak-equivalence-classes: that is Kechris's monotonicity for finitely generated groups only; this is the same monotonicity for every countable group, including the case of finite cost against infinite cost, and relative to any subgroup.
  fpbs-bernoulli-maximal-cost: that is Bernoulli maximality for finitely generated groups; this proves it for every countably infinite group.
  fpbs-finite-cost-groups-free-actions-have-finite-cost: that asks every free action to have finite cost once one does; this transfers finite cost only upward along weak containment, which reduces that node to the Bernoulli shift but does not prove it.
  burton-kechris-cost-usc-and-maximum-action: that imports the conjugacy-closure form of weak containment and semicontinuity for finitely generated groups; this uses only the former, to prove monotonicity for all countable groups.
artifacts:
  - research/artifacts/fpbs-finite-cost-transfers-up-weak-containment-2026-09-18.md
---

**ESTABLISHED** through `fpbs-finite-cost-transfers-up-weak-containment-proof`.

Let `Γ` be a countable group and `H ≤ Γ` any subgroup. Let `a`, `b` be p.m.p.
actions of `Γ` on standard non-atomic spaces, with `a` free and `a ≼ b`. Then

```text
relC( E_b ; E_{b|H} )  ≤  relC( E_a ; E_{a|H} ),        in particular  C(b) ≤ C(a).
```

This answers Burton–Kechris Problem 7.4 (arXiv:1611.07921v5), "Does
Theorem 7.1 hold for arbitrary groups?", in the affirmative. Tucker-Drob
(Cor 6.22) had proved it under the hypothesis `C(b) < ∞`.

**Consequences** (artifact §4). Let `Γ` be countably infinite and `s_Γ` a
nontrivial Bernoulli shift.

- Every free action `a` has `C(a) ≤ C(s_Γ)`, and
  `relC(E_a; E_{a|H}) ≤ relC(E_{s_Γ}; E_{s_Γ|H})`. Cost is constant on
  weak-equivalence classes of free actions.
- `Γ` has fixed price iff `C(s_Γ) = C(Γ)`. So `fpbs-fixed-price-universal` is
  the single reverse inequality `C(a) ≥ C(s_Γ)`, for every countable group,
  with no passage from finitely generated groups needed.
- `fpbs-finite-cost-groups-free-actions-have-finite-cost` is equivalent to:
  `C(Γ) < ∞` implies `C(s_Γ) < ∞`.
- For locally free `Γ`, `fpbs-locally-free-free-actions-have-finite-cost` is
  equivalent to `C(s_Γ) < ∞`.
- For `Gamma_mal`: `fpbs-mal-fixed-price-iff-bernoulli-finite-cost`.

**Proof idea.**
1. Take a cheap graphing `Φ` of `E_a` over `E_{a|H}`, and exhaust `Γ` by
   `H_n = ⟨H, γ'_1, …, γ'_n⟩`.
2. The pieces of `Φ` with labels outside `H_n` have mass `t_n → 0`. Pass to a
   subsequence with summable tails.
3. At stage `k`, finitely many words in `H_{n_k}` and tail pieces reach each
   new generator on almost all of `X`. This is where freeness of `a` is used.
4. Transfer these finitely many patterns to `b` with a fresh conjugator, by
   the conjugacy-closure form of `≼`, and add small fix-up pieces.
5. Relative to the already-built `E_{b|H_{n_k}}`, each stage costs its tail
   plus `ε 2^{-k}`.

Artifact: `research/artifacts/fpbs-finite-cost-transfers-up-weak-containment-2026-09-18.md`.
