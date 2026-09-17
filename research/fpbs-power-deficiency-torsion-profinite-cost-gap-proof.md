---
rg: 2
id: fpbs-power-deficiency-torsion-profinite-cost-gap-proof
kind: route
title: Count the power p-deficiency, lift finite-index subgroups to subnormal p-power index, compare mod-p ranks, and apply Abert-Nikolov
target: fpbs-power-deficiency-torsion-profinite-cost-gap
requires:
  - fpbs-power-p-deficiency-schreier-bound
  - fpbs-abert-nikolov-rank-gradient-equals-profinite-cost
  - fpbs-kazhdan-cofinal-mod-p-growth-vanishes
  - fg-rf-bounded-exponent-groups-are-finite
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

The written proof is Section 3 of the linked note.

- **Deficiency.** `def_p(Gamma) >= 1 - sum_{i>=1} p^{-(i+1)} = delta`.
- **Subnormality.** Every finite quotient of the `p`-torsion group `Gamma'` is
  a `p`-group. So a finite-index `U'` is subnormal of `p`-power index, and
  so is its preimage `U`.
- **Mod-p rank.** `[U,U]U^p` is subnormal of `p`-power index in `Gamma`, so
  it is open in the pro-`p` topology (Ershov, Golod-Shafarevich survey,
  Section 9, remark after the definition of the p-gradient) and contains the
  kernel. Hence `d_p(U') = d_p(U) >= 1 + delta[Gamma:U]`.
- **Rank.** `d >= d_p`.
- **Cost.** Abert--Nikolov converts the gradient bound into the cost bound.
- **Exponent and (T).** Unbounded exponent is restricted Burnside.
  No property (T): with `c = delta`, `fpbs-kazhdan-cofinal-mod-p-growth-vanishes`
  gives a finite-index `M` whose normal finite-index subgroups `N` have
  `d_p(N) < delta[Gamma':N]`, against `d_p(N) >= 1 + delta[Gamma':N]`.

The survey's Corollary 9.2 proof states the gradient bound verbatim: "Thus,
Q′ is a residually finite group with positive rank gradient".

This is a written deduction, not a formal verification.
