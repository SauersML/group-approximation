---
rg: 2
id: fpbs-mal-promotion-cost-monotone-under-weak-containment
kind: claim
title: Promotion cost with arbitrary labels is antitone under weak containment of free actions, so the Gamma_mal floor holds iff each depth has some free F_2-action with promotion cost at least a fixed c > 0
distinct_from:
  fpbs-finite-cost-transfers-up-weak-containment: that transfers relC(E_a; E_{a|H}) over the whole orbit relation; this transfers the cost of promoting E_{a|H'} to E_{a|H} for H finitely generated over H' and H ≠ Γ, with graphings allowed to use labels outside H.
  fpbs-mal-floor-iff-deep-promotion-floor: that reduces the floor to inf_j Q_j(ρ) > 0 for the Bernoulli shift ρ of F_2; this shows Q_j(ρ) is the maximum of Q_j over all free actions of F_2, so the floor needs only a separate free witness at each depth.
  fpbs-mal-bernoulli-single-stage-floor: that is the open target; this is an equivalent relaxation of it and decides nothing.
artifacts:
  - research/artifacts/fpbs-promotion-cost-weak-containment-2026-09-18.md
---

**ESTABLISHED** through `fpbs-mal-promotion-cost-monotone-under-weak-containment-proof`.

For `H' ≤ H ≤ Γ` and a p.m.p. action `a` of `Γ`, the *promotion cost*
`P(a; H', H)` is the infimum of the costs of labelled graphings `Φ` of `a`,
with labels anywhere in `Γ`, such that `E_{a|H'} ∨ Φ ⊇ E_{a|H}`.

**Theorem M.** Let `H = ⟨H', F⟩` with `F` finite. Let `a ≼ b` be actions on
standard non-atomic spaces, with `a` free. Then

```text
P(b; H', H)  ≤  P(a; H', H).
```

**Depth costs.** Let `L = F(a, b)`, `φ(b) = b a b^{-2}`, `L_j = φ^j(L)`,
`Q_j(c) = P(c; L_{j+1}, L_j)`, and let `ρ` be the Bernoulli shift of `L`.
For every free action `c` of `L`:

- `Q_j(c) ≤ Q_j(ρ)`, with equality when `c ≼ ρ`;
- `Q_j(c) ≤ relC(E_{c|L_j}; E_{c|L_{j+1}}) ≤ Q_0(ρ)`.

**Per-depth witnesses.** `fpbs-mal-bernoulli-single-stage-floor` holds iff
there is `c > 0` such that, for every `j`, **some** free p.m.p. action `a_j`
of `F_2` on a standard non-atomic space has `Q_j(a_j) ≥ c`. The `a_j` may be
unrelated to each other, non-ergodic and profinite. They need not extend to
`Gamma_mal`. The floor fails iff actions weakly contained in `ρ` have
arbitrarily cheap promotions at some depth.

**Profinite witnesses** (artifact §3, Proposition F). For a free profinite
action along `N_n`, `Q_j = lim_n Q_j^{(n)}`, where `Q_j^{(n)}` is a finite
covering problem: normalised size of `G_n`-coloured label sets realising
`t_j = φ^j(b)` over `L_{j+1}` at every `x ∈ G_n`.

**Reading.** Lower bounds for the floor no longer need Bernoulli structure.
Only the refutation side is tied to the Bernoulli weak class. No witness can
exceed `ρ` itself, so witnesses are proof devices, not extra cost.
