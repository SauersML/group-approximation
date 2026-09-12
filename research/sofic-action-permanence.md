---
rg: 2
id: sofic-action-permanence
kind: route
title: Wreath-product permanence theorems (Hayes–Sale, GKP, Alekseev–Bradford)
target: hyperlinear-wreath-model
requires: []
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Wreath-product permanence theorems

Get hyperlinearity of `W` for free from a permanence theorem for wreath
products, rather than by building microstates. Dead: every such theorem takes
the soficity of the coordinate action as its hypothesis, and that hypothesis is
refuted (`coordinate-action-not-sofic`).

The three candidates, all read verbatim in their authors' own source and
transcribed in the artifact:

- **Hayes–Sale**, arXiv:1608.02610, Theorem 1.3(ii): `G` hyperlinear and `H`
  sofic ⟹ `G ≀ H` hyperlinear. Not applicable at all — the paper's `G ≀ H` is
  the **standard** wreath product `⊕_H G ⋊ H`, fixed as such immediately before
  Theorem 1.1. Permutational wreath products occur in that paper only as an
  internal approximation device, and it has no theorem with a hypothesis on a
  general action. (The id `1601.xxxxx` used elsewhere in the corpus is wrong.)
- **Gao–Kunnawalkam Elayavalli–Patchell**, arXiv:2401.04945, Theorem 3.8: `M`
  Connes-embeddable, `H` hyperlinear, `α : H ↷ X` a **sofic action** ⟹
  `M ≀_α H` Connes-embeddable. This is the right shape and the right generality
  — with `M = ℂ ⊕ ℂ` and `H = G` its conclusion is precisely Connes
  embeddability of `M_KT`, i.e. hyperlinearity of `W`. The hypothesis is
  exactly what `coordinate-action-not-sofic` refutes.
- **Alekseev–Bradford**, arXiv:2601.18742, Corollary 5.2/5.5: same shape, via
  sofic `𝒞`-actions and halo products; blocked identically.

The one known sufficient condition for the hypothesis — amenable point
stabilizers — fails as badly as it can: the stabilizers are conjugates of `Γ`,
infinite with property (T).

**What this route is worth even though it is dead.** It fixes the price of
admission. The lamp side and the acting side are both free: `ℂ ⊕ ℂ` is
hyperfinite and `G` is residually finite, hence sofic, hence hyperlinear. All
of the difficulty in `hyperlinear-wreath-model` is concentrated in the
*action*, and specifically in the one datum a permanence theorem needs and
cannot have. A model must therefore supply, by hand, something no permanence
theorem can supply: an embedding of the Bernoulli lamp algebra that is not
normalized by permutations.

The same refuted hypothesis also cuts the other way: run through the
diagonal-coset construction (`nonsofic-orbit-forces-commuting-counterexample`)
it *answers* a published question rather than blocking a route — GKP
Question 4.2 on commuting sofic actions is false
(`commuting-sofic-actions-need-not-combine`).
